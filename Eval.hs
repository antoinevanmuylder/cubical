{-# LANGUAGE CPP #-}
module Eval ( eval
            , evals
            , app
            , conv
            , fstSVal
            ) where

import Control.Arrow (second)
import Data.List
import Data.Maybe (fromMaybe)
import qualified Debug.Trace as DT

import CTT

debug :: Bool
#ifdef debugmode
debug = True
#else
debug = False
#endif

trace :: String -> a -> a
trace s e = if debug then DT.trace s e else e

look :: Ident -> OEnv -> (Binder, Val)
look x (OEnv (Pair rho (n@(y,l),u)) opaques)
  | x == y    = (n, u)
  | otherwise = look x (OEnv rho opaques)
look x r@(OEnv (PDef es r1) o) = case lookupIdent x es of
  Just (y,t)  -> (y,eval r t)
  Nothing     -> look x (OEnv r1 o)

eval :: OEnv -> Ter -> Val
eval e U                 = VU
eval e (PN pn)           = evalAppPN e pn []
eval e t@(App r s)       = case unApps t of
  (PN pn,us) -> evalAppPN e pn us
  _          -> app (eval e r) (eval e s)
eval e (Var i)           =
  let (x,v) = look i e
  in if x `elem` opaques e then VVar ("opaque_" ++ show x) $ support v else v
eval e (Pi a b)          = VPi (eval e a) (eval e b)
eval e (Lam x t)         = Ter (Lam x t) e -- stop at lambdas
eval e (Sigma a b)       = VSigma (eval e a) (eval e b)
eval e (SPair a b)       = VSPair (eval e a) (eval e b)
eval e (Fst a)           = fstSVal $ eval e a
eval e (Snd a)           = sndSVal $ eval e a
eval e (Where t decls)   = eval (oPDef False decls e) t
eval e (Con name ts)     = VCon name $ map (eval e) ts
eval e (Split pr alts)   = Ter (Split pr alts) e
eval e (Sum pr ntss)     = Ter (Sum pr ntss) e

evals :: OEnv -> [(Binder,Ter)] -> [(Binder,Val)]
evals env = map (second (eval env))

fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a b)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair a b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

-- Application
app :: Val -> Val -> Val
app (Ter (Lam x t) e) u                         = eval (oPair e (x,u)) t
app u1@(Kan Com (VPi a b) box@(Box dir x v nvs)) u =
  trace "Pi Com" $
  let z     = fresh (u1,u)
      box'  = swap box x z
      ufill = fill (swap a x z) (Box (mirror dir) z u [])
      bcu   = cubeToBox ufill (shapeOfBox box')
  in com (app (swap b x z) ufill) (appBox box' bcu)
app kf@(Kan Fill (VPi a b) box@(Box dir i w nws)) v =
  trace "Pi fill" $
  let x     = fresh (kf, v)
      u     = v `face` (i,dir)
      ufill = fill a (Box (mirror dir) i u [])
      bcu   = cubeToBox ufill (shapeOfBox box)
      vfill = fill a (Box (mirror dir) i u [((x,down),ufill),((x,up),v)])
      vx    = fill (app b ufill) (appBox box bcu)
      vi0   = app w (vfill `face` (i,mirror dir))
      vi1   = com (app b ufill) (appBox box bcu)
      nvs   = [ ((n,d),app ws (vfill `face` (n,d)))
              | ((n,d),ws) <- nws ]
  in com (app b vfill) (Box up x vx (((i,mirror dir),vi0) : ((i,dir),vi1):nvs))
-- app vext@(VExt x bv fv gv pv) w = do
--   -- NB: there are various choices how to construct this
--   let y = fresh (vext, w)
--   w0    <- w `face` (x,down)
--   left  <- app fv w0
--   right <- app gv (swap w x y)
--   pvxw  <- appNameM (app pv w0) x
--   comM (app bv w) (return (Box up y pvxw [((x,down),left),((x,up),right)]))
app vhext@(VHExt x bv fv gv pv) w =
  let a0 = w `face` (x,down)
      a1 = w `face` (x,up)
  in appName (apps pv [a0, a1, Path x w]) x
app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t)  -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter (Split _ _) _) v
  | isNeutral v = VSplit u v -- v should be neutral
  | otherwise   = error $ "app: (VSplit) " ++ show v ++ " is not neutral"
app r s
  | isNeutral r = VApp r s -- r should be neutral
  | otherwise   = error $ "app: (VApp) " ++ show r ++ " is not neutral"

apps :: Val -> [Val] -> Val
apps = foldl app

appBox :: Box Val -> Box Val -> Box Val
appBox (Box dir x v nvs) (Box _ _ u nus) =
  let lookup' x = fromMaybe (error "appBox") . lookup x
  in Box dir x (app v u) [ (nnd,app v (lookup' nnd nus))
                         | (nnd,v) <- nvs ]

appName :: Val -> Name -> Val
appName (Path x u) y | y `elem` [0,1] = u `face` (x,y)
appName p y          | y `elem` [0,1] = VAppName p y -- p has to be neutral
appName (Path x u) y | x == y             = u
                     | y `elem` support u = error ("appName " ++ "\nu = " ++
                                                   show u ++ "\ny = " ++ show y)
                     | otherwise          = swap u x y
appName v y          = VAppName v y

-- Apply a primitive notion
evalAppPN :: OEnv -> PN -> [Ter] -> Val
evalAppPN e pn ts
  | length ts < arity pn =
      -- Eta expand primitive notions
      let r       = arity pn - length ts
          binders = map (\n -> '_' : show n) [1..r]
          vars    = map Var binders
      in Ter (mkLams binders $ mkApps (PN pn) (ts ++ vars)) e
  | otherwise =
      let (args,rest) = splitAt (arity pn) ts
          vas = map (eval e) args
          p   = evalPN (freshs e) pn vas
          r   = map (eval e) rest
      in apps p r

-- Evaluate primitive notions
evalPN :: [Name] -> PN -> [Val] -> Val
evalPN (x:_) Id            [a,a0,a1]     = VId (Path x a) a0 a1
evalPN (x:_) IdP           [_,_,p,a0,a1] = VId p a0 a1
evalPN (x:_) Refl          [_,a]         = Path x a
evalPN (x:_) TransU        [_,_,p,t]     = com (appName p x) (Box up x t [])
evalPN (x:_) TransInvU     [_,_,p,t]     = com (appName p x) (Box down x t [])
evalPN (x:_) TransURef     [a,t]         = Path x $ fill a (Box up x t [])
evalPN (x:_) TransUEquivEq [_,b,f,_,_,u] =
  Path x $ fill b (Box up x (app f u) [])   -- TODO: Check this!
evalPN (x:y:_) CSingl [a,u,v,p] =
  let pv    = appName p y
      theta = fill a (Box up y u [((x,down),u),((x,up),pv)])
      omega = theta `face` (y,up)
  in Path x (VSPair omega (Path y theta))
-- evalPN (x:_)   Ext        [_,b,f,g,p]   = return $ Path x $ VExt x b f g p
evalPN (x:_)   HExt       [_,b,f,g,p]   = Path x $ VHExt x b f g p
evalPN _       Inh        [a]           = VInh a
evalPN _       Inc        [_,t]         = VInc t
evalPN (x:_)   Squash     [_,r,s]       = Path x $ VSquash x r s
evalPN _       InhRec     [_,b,p,phi,a] = inhrec b p phi a
evalPN (x:_)   EquivEq    [a,b,f,s,t]   = Path x $ VEquivEq x a b f s t
evalPN (x:y:_) EquivEqRef [a,s,t]       =
  Path y $ Path x $ VEquivSquare x y a s t
evalPN (x:_)   MapOnPath  [_,_,f,_,_,p]    = Path x $ app f (appName p x)
evalPN (x:_)   MapOnPathD [_,_,f,_,_,p]    = Path x $ app f (appName p x)
evalPN (x:_)   AppOnPath [_,_,_,_,_,_,p,q] =
  Path x $ app (appName p x) (appName q x)
evalPN (x:_)   MapOnPathS [_,_,_,f,_,_,p,_,_,q] =
  Path x $ app (app f (appName p x)) (appName q x)
evalPN _       Circle     []               = VCircle
evalPN _       Base       []               = VBase
evalPN (x:_)   Loop       []               = Path x $ VLoop x
evalPN _       CircleRec  [f,b,l,s]        = circlerec f b l s
evalPN _       I          []               = VI
evalPN _       I0         []               = VI0
evalPN _       I1         []               = VI1
evalPN (x:_)   Line       []               = Path x $ VLine x
evalPN _       IntRec     [f,s,e,l,u]      = intrec f s e l u
evalPN _       u          _                = error ("evalPN " ++ show u)

-- appS1 :: Val -> Val -> Name -> Eval Val
-- appS1 f p x | x `elem` [0,1] = appName p x
-- appS1 f p x = do
--   let y = fresh (p,(f,x))
--   q <- appName p y
--   a <- appName p 0
--   b <- appName p 1
--   newBox <- Box down y b <$>
--             sequenceSnd  [ ((x,down),q `face` (x,down))
--                          , ((x,up),b `face` (x,up))]
--   fb <- app f VBase
--   fl <- app f (VLoop y)
--   tu <- fillM (return VU) (Box down y fb <$>
--                            sequenceSnd [ ((x,down),fl `face` (x,down))
--                                        , ((x,up),fb `face` (x,up))])
--   com tu newBox

-- Compute the face of an environment
faceEnv :: OEnv -> Side -> OEnv
faceEnv e xd = mapOEnv (`face` xd) e

faceName :: Name -> Side -> Name
faceName 0 _                 = 0
faceName 1 _                 = 1
faceName x (y,d) | x == y    = d
                 | otherwise = x

-- -- Compute the face of a value
face :: Val -> Side -> Val
face u xdir@(x,dir) =
  let fc v = v `face` xdir in case u of
  VU      -> VU
  Ter t e -> eval (e `faceEnv` xdir) t
  VId a v0 v1 -> VId (fc a) (fc v0) (fc v1)
  Path y v | x == y    -> u
           | otherwise -> Path y (fc v)
  -- VExt y b f g p | x == y && dir == down -> f
  --                | x == y && dir == up   -> g
  --                | otherwise             ->
  --                  VExt y <$> fc b <*> fc f <*> fc g <*> fc p
  VHExt y b f g p | x == y && dir == down -> f
                  | x == y && dir == up   -> g
                  | otherwise             -> VHExt y (fc b) (fc f) (fc g) (fc p)
  VPi a f    -> VPi (fc a) (fc f)
  VSigma a f -> VSigma (fc a) (fc f)
  VSPair a b -> VSPair (fc a) (fc b)
  VInh v     -> VInh (fc v)
  VInc v     -> VInc (fc v)
  VSquash y v0 v1 | x == y && dir == down -> v0
                  | x == y && dir == up   -> v1
                  | otherwise             -> VSquash y (fc v0) (fc v1)
  VCon c us -> VCon c $ map fc us
  VEquivEq y a b f s t | x == y && dir == down -> a
                       | x == y && dir == up   -> b
                       | otherwise             ->
                         VEquivEq y (fc a) (fc b) (fc f) (fc s) (fc t)
  VPair y a v | x == y && dir == down -> a
              | x == y && dir == up   -> fc v
              | otherwise             -> VPair y (fc a) (fc v)
  VEquivSquare y z a s t | x == y                -> a
                         | x == z && dir == down -> a
                         | x == z && dir == up   ->
                           let idV = Ter (Lam (noLoc "x") (Var "x")) oEmpty
                           in VEquivEq y a a idV s t
                         | otherwise             ->
                          VEquivSquare y z (fc a) (fc s) (fc t)
  VSquare y z v | x == y                -> fc v
                | x == z && dir == down -> fc v
                | x == z && dir == up   ->
                  let v' = fc v
                  in VPair y (v' `face` (y,down)) v'
                | otherwise             -> VSquare y z $ fc v
  Kan Fill a b@(Box dir' y v nvs)
    | x /= y && x `notElem` nonPrincipal b -> fill (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b              -> lookBox (x,dir) b
    | x == y && dir == mirror dir'         -> v
    | otherwise                            -> com a b
  VFillN a b@(Box dir' y v nvs)
    | x /= y && x `notElem` nonPrincipal b -> fill (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b              -> lookBox (x,dir) b
    | x == y && dir == mirror dir'         -> v
    | otherwise                            -> com a b
  Kan Com a b@(Box dir' y v nvs)
    | x == y                     -> u
    | x `notElem` nonPrincipal b -> com (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
  VComN a b@(Box dir' y v nvs)
    | x == y                     -> u
    | x `notElem` nonPrincipal b -> com (fc a) (mapBox fc b)
    | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
  VComp b@(Box dir' y _ _)
    | x == y                     -> u
    | x `notElem` nonPrincipal b -> VComp $ mapBox fc b
    | x `elem` nonPrincipal b    -> lookBox (x,dir) b `face` (y,dir')
  VFill z b@(Box dir' y v nvs)
    | x == z                               -> u
    | x /= y && x `notElem` nonPrincipal b -> VFill z $ mapBox fc b
    | (x,dir) `elem` defBox b              ->
      lookBox (x,dir) (mapBox (`face` (z,down)) b)
    | x == y && dir == dir'                ->
        VComp (mapBox (`face` (z,up)) b)
  VInhRec b p h a     -> inhrec (fc b) (fc p) (fc h) (fc a)
  VApp u v            -> app (fc u) (fc v)
  VAppName u n        -> appName (fc u) (faceName n xdir)
  VSplit u v          -> app (fc u) (fc v)
  VVar s d            -> VVar s [ faceName n xdir | n <- d ]
  VFst p              -> fstSVal $ fc p
  VSnd p              -> sndSVal $ fc p
  VCircle             -> VCircle
  VBase               -> VBase
  VLoop y | x == y    -> VBase
          | otherwise -> VLoop y
  VCircleRec f b l s  -> circlerec (fc f) (fc b) (fc l) (fc s)
  VI  -> VI
  VI0 -> VI0
  VI1 -> VI1
  VLine y
    | x == y && dir == down -> VI0
    | x == y && dir == up   -> VI1
    | otherwise             -> VLine y
  VIntRec f s e l u -> intrec (fc f) (fc s) (fc e) (fc l) (fc u)

unCompAs :: Val -> Name -> Box Val
unCompAs (VComp box) y = swap box (pname box) y
unCompAs v           _ = error $ "unCompAs: " ++ show v ++ " is not a VComp"

unFillAs :: Val -> Name -> Box Val
unFillAs (VFill x box) y = swap box x y
unFillAs v             _ = error $ "unFillAs: " ++ show v ++ " is not a VFill"

-- p(x) = <z>q(x,z)
-- a(x) = q(x,0)     b(x) = q(x,1)
-- q(0,y) connects a(0) and b(0)
-- we connect q(0,0) to q(1,1)
-- appDiag :: Val -> Val -> Name -> Val
-- appDiag tu p x | x `elem` [0,1] = appName p x
-- appDiag tu p x =
-- traceb ("appDiag " ++ "\ntu = " ++ show tu ++ "\np = " ++ show p ++ "\nx = "
-- --                       ++ show x ++ " " ++ show y
-- --                       ++ "\nq = " ++ show q) -- "\nnewBox =" ++ show newBox)
--  com tu newBox
--    where y = fresh (p,(tu,x))
--          q = appName p y
--          a = appName p 0
--          b = appName p 1
--          newBox = Box down y b [((x,down),q `face` (x,down)),((x,up),b `face` (x,up))]

cubeToBox :: Val -> Box () -> Box Val
cubeToBox v = modBox (\nd _ -> v `face` nd)

inhrec :: Val -> Val -> Val -> Val -> Val
inhrec _ _ phi (VInc a)          = app phi a
inhrec b p phi (VSquash x a0 a1) =
  let fc w d   = w `face` (x,d)
      b0       = inhrec (fc b down) (fc p down) (fc phi down) a0
      b1       = inhrec (fc b up) (fc p up) (fc phi up) a1
      z        = fresh [b,p,phi,b0,b1]
      b0fill   = fill b (Box up x b0 [])
      b0fillx1 = b0fill `face` (x, up)
      right    = appName (app (app (fc p up) b0fillx1) b1) z
  in com b (Box up z b0fill [((x,down),b0),((x,up),right)])
inhrec b p phi (Kan ktype (VInh a) box) =
  let irec (j,dir) v = let fc v = v `face` (j,dir)
                       in inhrec (fc b) (fc p) (fc phi) v
      box' = modBox irec box
  in kan ktype b box'
inhrec b p phi v = VInhRec b p phi v -- v should be neutral

circlerec :: Val -> Val -> Val -> Val -> Val
circlerec _ b _ VBase       = b
circlerec f b l v@(VLoop x) =
  let y     = fresh [f,b,l,v]
      pxy   = appName l y
      theta = connection VCircle x y v
      a     = app f theta
      px1   = pxy `face` (y,up)
      p11   = px1 `face` (x,up)
      p0y   = pxy `face` (x,down)
  in com a (Box down y px1 [((x,down),p0y),((x,up),p11)])
circlerec f b l v@(Kan ktype VCircle box) = kan ktype ffillv box'
  where y = fresh [f,b,l,v]
        boxxy = swap box (pname box) y
        crec side = let fc w = w `face` side
                    in circlerec (fc f) (fc b) (fc l)
        ffillv = app f (Kan Fill VCircle boxxy)
        box'   = modBox crec boxxy
circlerec f b l v = VCircleRec f b l v -- v should be neutral

-- Assumes y is fresh and x fresh for a; constructs a connection
-- square with faces u (x), u (y), u (1), u (1).
connection :: Val -> Name -> Name -> Val -> Val
connection a x y u =
  let u1      = u `face` (x,up)
      ufill   = fill a (Box down y u1 [((x,down), swap u x y), ((x,up),u1)])
      z       = fresh ([x,y], [a,u])
      ufillzy = swap ufill x z
      ufillzx = swap ufillzy y x
  in com a (Box down z u1 [ ((x,down),ufillzy), ((x,up),u1)
                          , ((y,down),ufillzx), ((y,up),u1)])

intrec :: Val -> Val -> Val -> Val -> Val -> Val
intrec _ s _ _ VI0         = s
intrec _ _ e _ VI1         = e
intrec f s e l v@(VLine x) =
  let y     = fresh [f,s,e,l,v]
      pxy   = appName l y
      theta = connection VI x y v
      a     = app f theta
      px1   = pxy `face` (y,up)
      p11   = px1 `face` (x,up)
      p0y   = pxy `face` (x,down)
  in com a (Box down y px1 [((x,down),p0y),((x,up),p11)])
intrec f s e l v@(Kan ktype VCircle box) =
  let irec side u = let fc w = w `face` side
                    in intrec (fc f) (fc s) (fc e) (fc l) u
      fv   = app f v
      box' = modBox irec box
  in kan ktype fv box'
intrec f s e l v = VIntRec f s e l v -- v should be neutral

kan :: KanType -> Val -> Box Val -> Val
kan Fill = fill
kan Com  = com

isNeutralFill :: Val -> Box Val -> Bool
isNeutralFill v box | isNeutral v               = True
isNeutralFill v@(Ter (PN (Undef _)) _) box      = True
isNeutralFill (Ter (Sum _ _) _) (Box _ _ v nvs) =
 isNeutral v || or [ isNeutral u | (_,u) <- nvs ]
isNeutralFill v@(Kan Com VU tbox') box@(Box d x _ _) = do
  let nK  = nonPrincipal tbox'
      nJ  = nonPrincipal box
      nL  = nJ \\ nK
      aDs = if x `elem` nK then allDirs nL else (x,mirror d):allDirs nL
  or [ isNeutral (lookBox yc box) | yc <- aDs ]
isNeutralFill v@(Kan Fill VU tbox) box =
  or [ isNeutral (lookBox yc box) | yc <- defBox box \\ defBox tbox ]
isNeutralFill v@(VEquivSquare y z _ _ _) box@(Box d x _ _) = do
  let nJ  = nonPrincipal box
      nL  = nJ \\ [y,z]
      aDs = if x `elem` [y,z] then allDirs nL else (x,mirror d) : allDirs nL
  or [ isNeutral (lookBox yc box) | yc <- aDs ]
isNeutralFill v@(VEquivEq z a b f s t) box@(Box d x vx nxs)
  | d == down && z == x = isNeutral $ app s vx
  | otherwise           = -- TODO: check
    let nJ  = nonPrincipal box
        nL  = nJ \\ [z]
        aDs = if x == z then allDirs nL else (x,mirror d) : allDirs nL
    in or [ isNeutral (lookBox yc box) | yc <- aDs ]
isNeutralFill v box = False

-- TODO: Simplify?
fills :: [(Binder,Ter)] -> OEnv -> [Box Val] -> [Val]
fills []         _ []          = []
fills ((x,a):as) e (box:boxes) =
  let v  = fill (eval e a) box
      vs = fills as (oPair e (x,v)) boxes
  in v : vs
fills _ _ _ = error "fills: different lengths of types and values"

unPack :: Name -> Name -> (Name,Dir) -> Val -> Val
unPack x y (z,c) v | z /= x && z /= y  = unSquare v
                   | z == y && c == up = sndVal v
                   | otherwise         = v

-- -- Kan filling
fill :: Val -> Box Val -> Val
fill v box | isNeutralFill v box = VFillN v box
fill vid@(VId a v0 v1) box@(Box dir i v nvs) =
  let x = fresh (vid, box)
      box' = consBox (x,(v0,v1)) (mapBox (`appName` x) box)
  in Path x $ fill (a `appName` x) box'
fill (VSigma a f) box@(Box dir x v nvs) =
  let u = fill a (mapBox fstSVal box)
  in VSPair u $ fill (app f u) (mapBox sndSVal box)
-- assumes cvs are constructor vals
fill v@(Ter (Sum _ nass) env) box@(Box _ _ (VCon n _) _) = case getIdent n nass of
  Just as ->
    let boxes = transposeBox $ mapBox unCon box
    -- fill boxes for each argument position of the constructor
    in VCon n $ fills as env boxes
  Nothing -> error $ "fill: missing constructor in labelled sum " ++ n
fill (VEquivSquare x y a s t) box@(Box dir x' vx' nvs) =
  VSquare x y $ fill a (modBox (unPack x y) box)
fill veq@(VEquivEq x a b f s t) box@(Box dir z vz nvs)
  | x /= z && x `notElem` nonPrincipal box =
    trace "VEquivEq case 1" $
    let ax0 = fill a (mapBox fstVal box)
        bx0 = app f ax0
        bx  = mapBox sndVal box
        bx' = mapBox (`face` (x,up)) bx
        bx1 = fill b bx'        --- independent of x
        v   = fill b $ (x,(bx0,bx1)) `consBox` bx
    in VPair x ax0 v
  | x /= z && x `elem` nonPrincipal box =
    trace "VEquivEq case 2" $
    let ax0 = lookBox (x,down) box

        -- modification function
        mf (ny,dy) vy | x /= ny    = sndVal vy
                      | dy == down = app f ax0
                      | otherwise  = vy

        bx  = modBox mf box
    in VPair x ax0 (fill b bx)
  | x == z && dir == up =
    trace "VEquivEq case 3" $
    let ax0 = vz
        bx0 = app f ax0
        v   = fill b $ Box dir z bx0 [ (nnd,sndVal v) | (nnd,v) <- nvs ]
    in VPair x ax0 v
  | x == z && dir == down =
    trace "VEquivEq case 4" $
    let gbsb    = app s vz
        (gb,sb) = (fstSVal gbsb, sndSVal gbsb)
        y       = fresh (veq, box)
        vy      = appName sb x

        vpTSq :: Name -> Dir -> Val -> (Val,Val)
        vpTSq nz dz (VPair z a0 v0) =
          let vp       = VSPair a0 (Path z v0)
              t0       = t `face` (nz,dz)
              b0       = vz `face` (nz,dz)
              l0sq0    = appName (app (app t0 b0) vp) y
              (l0,sq0) = (fstSVal l0sq0, sndSVal l0sq0)
              sq0x     = appName sq0 x
          in (l0,sq0x)  -- TODO: check the correctness of the square s0

        -- TODO: Use modBox!
        vsqs   = [ ((n,d),vpTSq n d v) | ((n,d),v) <- nvs]
        box1   = Box up y gb [ (nnd,v) | (nnd,(v,_)) <- vsqs ]
        afill  = fill a box1
        acom   = afill `face` (y,up)
        fafill = app f afill
        box2   = Box up y vy (((x,down),fafill) : ((x,up),vz) :
                            [ (nnd,v) | (nnd,(_,v)) <- vsqs ])
        bcom   = com b box2
    in VPair x acom bcom
  | otherwise = error "fill EqEquiv"
fill v@(Kan Com VU tbox') box@(Box dir x' vx' nvs')
  | toAdd /= [] = -- W.l.o.g. assume that box contains faces for
                  -- the non-principal sides of tbox.
    trace "Kan Com 1" $
    let add :: Side -> Val
        add yc = let box' = mapBox (`face` yc) box
                 in fill (lookBox yc tbox `face` (x,tdir)) box'

        sides' = [ (n,(add (n,down),add (n,up))) | n <- toAdd ]

     in fill v (sides' `appendBox` box)
  | x' `notElem` nK =
    trace "Kan Com 2" $
    let principal    = fill tx (mapBox (pickout (x,tdir')) boxL)
        nonprincipal =
          [ let pyc  = principal `face` yc
                side = [((x,tdir),lookBox yc box),((x,tdir'),pyc)]
                v'   = fill (lookBox yc tbox)
                            (side `appendSides` mapBox (pickout yc) boxL)
                in (yc,v')
          | yc <- allDirs nK ]
    in VComp (Box tdir x principal nonprincipal)
  | x' `elem` nK =
    trace "Kan Com 3" $
    let -- assumes zc in defBox tbox
        auxsides zc = [ (yd,pickout zc (lookBox yd box)) | yd <- allDirs nL ]

        -- extend input box along x with orientation tdir'; results
        -- in the non-principal faces on the intersection of defBox
        -- box and defBox tbox; note, that the intersection contains
        -- (x',dir'), but not (x',dir) (and (x,_))
        npintbox = modBox (\yc boxside -> fill (lookBox yc tbox)
                                          (Box tdir' x boxside (auxsides yc)))
                     (subBox (nK `intersect` nJ) box)

        npintfacebox = mapBox (`face` (x,tdir')) npintbox
        principal    = fill tx (auxsides (x,tdir') `appendSides` npintfacebox)
        nplp         = principal `face` (x',dir)
        fnpintboxs   = [ (yc,v `face` (x',dir)) | (yc,v) <- sides npintbox ]
        nplnp        = auxsides (x',dir) ++ fnpintboxs
        -- the missing non-principal face on side (x',dir)
        v'           = fill (lookBox (x',dir) tbox) (Box tdir x nplp nplnp)
        nplast       = ((x',dir),v')

    in VComp (Box tdir x principal (nplast:fromBox npintbox))
  where nK    = nonPrincipal tbox
        nJ    = nonPrincipal box
        z     = fresh (tbox', box)
        -- x is z
        tbox@(Box tdir x tx nvs) = swap tbox' (pname tbox') z
        toAdd = nK \\ (x' : nJ)
        nL    = nJ \\ nK
        boxL  = subBox nL box
        dir'  = mirror dir
        tdir' = mirror tdir
        -- asumes zd is in the sides of tbox
        pickout zd vcomp = lookBox zd (unCompAs vcomp z)
fill v@(Kan Fill VU tbox@(Box tdir x tx nvs)) box@(Box dir x' vx' nvs')
  -- the cases should be (in order):
  -- 1) W.l.o.g. K subset x', J
  -- 2) x' = x &  dir = tdir
  -- 3) x' = x &  dir = mirror tdir
  -- 4) x' `notElem` K
  -- 5) x' `elem` K
  | toAdd /= [] =
    -- W.l.o.g. x,nK subset x':nJ
    trace "Kan Fill VU Case 1" $
    let add :: Side -> Val
        add zc = fill (v `face` zc) (mapBox (`face` zc) box)

        newSides = [ (zc,add zc) | zc <- allDirs toAdd ]
    in fill v (newSides `appendSides` box)
  | x == x' && dir == tdir =
    -- assumes K subset x',J
    trace "Kan Fill VU Case 2" $
    let boxp = lookBox (x,dir') box  -- is vx'
        principal = fill (lookBox (x',tdir') tbox)
                         (Box up z boxp (auxsides (x',tdir')))
        nonprincipal =
          [ (zc,let principzc = lookBox zc box
                    fpzc = principal `face` zc
                    -- "degenerate" along z!
                    ppzc = principzc `face` (x,tdir)
                    sides = [((x,tdir'),fpzc),((x,tdir),ppzc)]
                in fill (lookBox zc tbox)
                        (Box up z principzc (sides ++ auxsides zc)))
          | zc <- allDirs nK ]
    in VFill z (Box tdir x principal nonprincipal)
  | x == x' && dir == mirror tdir =
    -- assumes K subset x',J
    trace "Kan Fill VU Case 3" $
    let -- the principal side of box must be a VComp
        -- should be safe given the neutral test at the beginning
        upperbox = unCompAs (lookBox (x,tdir) box) x
        nonprincipal =
          [ (zc,let top    = lookBox zc upperbox
                    bottom = lookBox zc box
                    princ  = top `face` (x,tdir) -- same as: bottom `face` (x,tdir)
                    sides  = [((z,down),bottom),((z,up),top)]
               in fill (lookBox zc tbox) (Box tdir' x princ -- "degenerate" along z!
                                       (sides ++ auxsides zc)))
          | zc <- allDirs nK ]
        nonprincipalfaces = [ (zc,u `face` (x,dir)) | (zc,u) <- nonprincipal ]
        principal         = fill (lookBox (x,tdir') tbox)
                             (Box up z (lookBox (x,tdir') upperbox)
                                       (nonprincipalfaces ++ auxsides (x,tdir')))
    in VFill z (Box tdir x principal nonprincipal)
  | x' `notElem` nK =
    -- assumes x,K subset x',J
    trace "Kan Fill VU Case 4" $
    let xaux      = unCompAs (lookBox (x,tdir) box) x
        boxprinc  = unFillAs (lookBox (x',dir') box) z
        princnp   = [((z,up),lookBox (x,tdir') xaux),
                     ((z,down),lookBox (x,tdir') box)]
                    ++ auxsides (x,tdir')
        principal = fill (lookBox (x,tdir') tbox) -- tx
                         (Box dir x' (lookBox (x,tdir') boxprinc) princnp)
        nonprincipal = [ let yup  = lookBox yc xaux
                             fyup = yup `face` (x,tdir)
                             np   = [ ((z,up),yup), ((z,down),lookBox yc box)
                                    , ((x,tdir), fyup) -- deg along z!
                                    , ((x,tdir'), principal `face` yc) ]
                                    ++ auxsides yc
                             fb   = fill (lookBox yc tbox)
                                         (Box dir x' (lookBox yc boxprinc) np)
                         in (yc, fb)
                       | yc <- allDirs nK]
    in VFill z (Box tdir x principal nonprincipal)
  | x' `elem` nK =
    -- assumes x,K subset x',J
    trace "Kan Fill VU Case 5" $
    -- surprisingly close to the last case of the Kan-Com-VU filling
    let upperbox = unCompAs (lookBox (x,tdir) box) x
        npintbox = modBox (\zc downside ->
                            let bottom = lookBox zc box
                                top    = lookBox zc upperbox
                                princ  = downside
                                         -- same as bottom `face` (x',tdir) and
                                         -- top `face` (x',tdir)
                                sides  = [((z,down),bottom),((z,up),top)]
                            in fill (lookBox zc tbox)
                                    (Box tdir' x princ (sides ++ auxsides zc)))
                   (subBox (nK `intersect` nJ) box)  -- intersection is nK - x'
        npint = fromBox npintbox
        npintfacebox = mapBox (`face` (x,tdir')) npintbox
        principalbox = ([ ((z,down),lookBox (x,tdir') box)
                        , ((z,up)  ,lookBox (x,tdir') upperbox)]
                        ++ auxsides (x,tdir'))
                       `appendSides` npintfacebox
        principal = fill tx principalbox
        nplp      = lookBox (x',dir) upperbox
        nplnp = [ ((x,tdir), nplp `face` (x',dir)) -- deg along z!
                , ((x,tdir'),principal `face` (x',dir)) ]
                ++ auxsides (x',dir)
                ++ [ (zc,u `face` (x',dir)) | (zc,u) <- sides npintbox ]
        fb = fill (lookBox (x',dir) tbox) (Box down z nplp nplnp)
    in VFill z (Box tdir x principal (((x',dir),fb) : npint))
    where z     = fresh (v, box)
          nK    = nonPrincipal tbox
          nJ    = nonPrincipal box
          toAdd = (x:nK) \\ (x' : nJ)
          nL    = nJ \\ (x : nK)
          dir'  = mirror dir
          tdir' = mirror tdir
          -- asumes zc is in the sides of tbox
          pickout zc vfill = lookBox zc (unFillAs vfill z)
          -- asumes zc is in the sides of tbox
          auxsides zc = [ (yd,pickout zc (lookBox yd box)) | yd <- allDirs nL ]
fill v b = Kan Fill v b

-- -- Composition (ie., the face of fill which is created)
com :: Val -> Box Val -> Val
com u box | isNeutralFill u box = VComN u box
com vid@VId{} box@(Box dir i _ _)         = fill vid box `face` (i,dir)
com vsigma@VSigma{} box@(Box dir i _ _)   = fill vsigma box `face` (i,dir)
com veq@VEquivEq{} box@(Box dir i _ _)    = fill veq box `face` (i,dir)
com u@(Kan Com VU _) box@(Box dir i _ _)  = fill u box `face` (i,dir)
com u@(Kan Fill VU _) box@(Box dir i _ _) = fill u box `face` (i,dir)
com ter@Ter{} box@(Box dir i _ _)         = fill ter box `face` (i,dir)
com v box                                 = Kan Com v box

conv :: Int -> Val -> Val -> Bool
conv k VU VU                                  = True
conv k (Ter (Lam x u) e) (Ter (Lam x' u') e') =
  let v = mkVar k $ support (e, e')
  in conv (k+1) (eval (oPair e (x,v)) u) (eval (oPair e' (x',v)) u')
conv k (Ter (Lam x u) e) u' =
  let v = mkVar k $ support (e,u')
  in conv (k+1) (eval (oPair e (x,v)) u) (app u' v)
conv k u' (Ter (Lam x u) e) =
  let v = mkVar k $ support (u',e)
  in conv (k+1) (app u' v) (eval (oPair e (x,v)) u)
conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
  (p == p') && convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
  (p == p') && convEnv k e e'
conv k (Ter (PN (Undef p)) e) (Ter (PN (Undef p')) e') =
  (p == p') && convEnv k e e'
conv k (VPi u v) (VPi u' v') =
  let w = mkVar k $ support [u,u',v,v']
  in conv k u u' && conv (k+1) (app v w) (app v' w)
conv k (VSigma u v) (VSigma u' v') =
  let w = mkVar k $ support [u,u',v,v']
  in conv k u u' && conv (k+1) (app v w) (app v' w)
conv k (VId a u v) (VId a' u' v') = and [conv k a a', conv k u u', conv k v v']
conv k (Path x u) (Path x' u')    = conv k (swap u x z) (swap u' x' z)
  where z = fresh (u,u')
conv k (Path x u) p'              = conv k (swap u x z) (appName p' z)
  where z = fresh u
conv k p (Path x' u')             = conv k (appName p z) (swap u' x' z)
  where z = fresh u'
-- conv k (VExt x b f g p) (VExt x' b' f' g' p') =
--   andM [x <==> x', conv k b b', conv k f f', conv k g g', conv k p p']
conv k (VHExt x b f g p) (VHExt x' b' f' g' p') =
  and [x == x', conv k b b', conv k f f', conv k g g', conv k p p']
conv k (VFst u) (VFst u')                     = conv k u u'
conv k (VSnd u) (VSnd u')                     = conv k u u'
conv k (VInh u) (VInh u')                     = conv k u u'
conv k (VInc u) (VInc u')                     = conv k u u'
conv k (VSquash x u v) (VSquash x' u' v')     =
  and [x == x', conv k u u', conv k v v']
conv k (VCon c us) (VCon c' us') = (c == c') && and (zipWith (conv k) us us')
conv k (Kan Fill v box) (Kan Fill v' box')    =
  conv k v v' && convBox k box box'
conv k (Kan Com v box) (Kan Com v' box')      =
  and [conv k (swap v x y) (swap v' x' y),
       convBox k (swap box x y) (swap box' x' y)]
  where y      = fresh ((v,v'),(box,box'))
        (x,x') = (pname box, pname box')
conv k (VComN v box) (VComN v' box')      =
  and [conv k (swap v x y) (swap v' x' y),
       convBox k (swap box x y) (swap box' x' y)]
  where y      = fresh ((v,v'),(box,box'))
        (x,x') = (pname box, pname box')
conv k (VFillN v box) (VFillN v' box')      =
  and [conv k v v', convBox k (swap box x y) (swap box' x' y)]
  where y      = fresh ((v,v'),(box,box'))
        (x,x') = (pname box, pname box')
conv k (VEquivEq x a b f s t) (VEquivEq x' a' b' f' s' t') =
  and [x == x', conv k a a', conv k b b',
       conv k f f', conv k s s', conv k t t']
conv k (VEquivSquare x y a s t) (VEquivSquare x' y' a' s' t') =
  and [x == x', y == y', conv k a a', conv k s s', conv k t t']
conv k (VPair x u v) (VPair x' u' v')     =
  and [x == x', conv k u u', conv k v v']
conv k (VSquare x y u) (VSquare x' y' u') =
  and [x == x', y == y', conv k u u']
conv k (VComp box) (VComp box')           =
  convBox k (swap box x y) (swap box' x' y)
  where y      = fresh (box,box')
        (x,x') = (pname box, pname box')
conv k (VFill x box) (VFill x' box')      =
  convBox k (swap box x y) (swap box' x' y)
  where y      = fresh (box,box')
conv k (VSPair u v)   (VSPair u' v')   = conv k u u' && conv k v v'
conv k (VSPair u v)   w                =
  conv k u (fstSVal w) && conv k v (sndSVal w)
conv k w              (VSPair u v)     =
  conv k (fstSVal w) u && conv k (sndSVal w) v
conv k (VApp u v)     (VApp u' v')     = conv k u u' && conv k v v'
conv k (VAppName u x) (VAppName u' x') = conv k u u' && (x == x')
conv k (VSplit u v)   (VSplit u' v')   = conv k u u' && conv k v v'
conv k (VVar x d)     (VVar x' d')     = (x == x') && (d == d')
conv k (VInhRec b p phi v) (VInhRec b' p' phi' v') =
  and [conv k b b', conv k p p', conv k phi phi', conv k v v']
conv k VCircle        VCircle          = True
conv k VBase          VBase            = True
conv k (VLoop x)      (VLoop y)        = x == y
conv k (VCircleRec f b l v) (VCircleRec f' b' l' v') =
  and [conv k f f', conv k b b', conv k l l', conv k v v']
conv k VI             VI               = True
conv k VI0            VI0              = True
conv k VI1            VI1              = True
conv k (VLine x)      (VLine y)        = x == y
conv k (VIntRec f s e l u) (VIntRec f' s' e' l' u') =
  and [conv k f f', conv k s s', conv k e e', conv k l l', conv k u u']
conv k _              _                = False

convBox :: Int -> Box Val -> Box Val -> Bool
convBox k box@(Box d pn _ ss) box'@(Box d' pn' _ ss') =
  if (d == d') && (pn == pn') && (sort np == sort np')
     then and [ conv k (lookBox s box) (lookBox s box')
              | s <- defBox box ]
     else False
  where (np, np') = (nonPrincipal box, nonPrincipal box')

convEnv :: Int -> OEnv -> OEnv -> Bool
convEnv k e e' = and $ zipWith (conv k) (valOfOEnv e) (valOfOEnv e')
