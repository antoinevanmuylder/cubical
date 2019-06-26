{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PatternSynonyms, LambdaCase #-}
module Eval where

import CTT
import Data.Monoid hiding (Sum)
import Data.List 

look :: Ident -> Env -> (Binder, Val)
look _ Empty = error "look: not found!"
look x (Pair rho (n@(y,_l),u))
  | x == y    = (n, u)
  | otherwise = look x rho
look x r@(PDef es r1) = case lookupIdent x es of
  Just (y,t)  -> (y,eval r t)
  Nothing     -> look x r1
look x (PCol rho _) = look x rho

lkCol :: Ident -> Env -> (Binder, CVal)
lkCol i (Pair e _) = lkCol i e
lkCol i (PDef _ e) = lkCol i e
lkCol i (PCol e (n@(j,_),v)) | i == j = (n,v)
                             | otherwise = lkCol i e
lkCol i Empty = error $ "Color " ++ show i ++ " not found"


reAbsEnvOnCol :: TColor -> Color -> Env -> Env
reAbsEnvOnCol _x _ Empty = Empty
reAbsEnvOnCol x i (Pair e (b,v)) = Pair (reAbsEnvOnCol x i e) (b, reabs)
  where reabs = clam i v
reAbsEnvOnCol x _i (PCol e ((x',_), _c)) | x == x' = e
reAbsEnvOnCol x i (PCol e c) = PCol (reAbsEnvOnCol x i e) c
reAbsEnvOnCol x i (PDef xas e) = PDef xas (reAbsEnvOnCol x i e) -- ???

reAbsWholeEnvOnCol :: TColor -> Color -> Env -> Env
reAbsWholeEnvOnCol x i e = reAbsEnvOnCol x i e

reconstruct :: Val -> Color -> [(Color,Val,Color)] -> Val
reconstruct v i edges = VSimplex ((i,v):[(j,f `app` v) | (i',f,j) <- edges, i'==i])

lift :: [(Color,CVal)] -> Val -> Color -> Val -> Val
lift ps v i t =
  let suspended = VLift ps v i t
      lft v' t' = lift ps v' i t'
  in case t of
   -- v : t[0/i]
   VPi _a f -> VLam $ \x -> lft (v `app` proj i x) (f `app` x)
   VU -> v
   VSimplexT is _tys edges -> cevals ps $ reconstruct w i edges
     where w = (projs (is \\ [i]) v)
   (Ter _ _) -> suspended
   (VSigma a f) -> VSPair l (lft (sndSVal v) (f `app` l))
     where l = lft (fstSVal v) a
   (VSPair _ _) -> error "lift: not a type (VSPair)"
   (VCon _ _) -> error "lift: not a type (VCon)"
   (VApp _ _) -> suspended
   (VSplit _ _) -> suspended
   (VVar _) -> suspended
   (VFst _) -> suspended
   (VSnd _) -> suspended
   (VLam _) -> error "lift: not a type (VLam)"
   (VCPi f) -> VCLam $ \j -> lft (v `capp` j) (f `capp` j)
   (VCLam _) -> error "lift: not a type (VCLam)"
   (VCApp _ _) -> suspended
   (VPath t' _) -> lft v t'
   (VLift _ _ _ _) -> suspended
   VSim ts -> vsim' (filter isntSimplex $ map (lift ps v i) ts)
   -- HACK: removing the simplices here. Simplices occur becaue we can have:
   -- Z : U <i/X> <j/Y>
   -- and so eval Z = <X,Y>
   -- We do this evaluation because we want Z@i@0 = X
   -- However this value isn't usable to do a lift.
   -- But on the other hand we can simply block and wait for the variable Z  to be substituted for a proper path between X and Y.
   _ -> suspended

isntSimplex :: Val -> Bool
isntSimplex (VSimplex _) = False
isntSimplex _ = True
  
eval :: Env -> Ter -> Val
eval _e U              = VU
eval e (Lift s i t) = case colEval e (CVar i) of
  Zero -> eval e s
  CVar i' -> lift [(j,colEval e (CVar j0)) | (j0,j) <- renaming]
                  (eval e' s) i' (eval e' t)
  where e' = mapEnv e
        mapEnv :: Env -> Env
        mapEnv = \case
          Empty -> Empty
          (Pair rho d) -> Pair (mapEnv rho) d
          (PDef d rho) -> PDef d (mapEnv rho)
          (PCol rho (b@(x,_),v)) -> PCol (mapEnv rho) $ (b,) $ case lookup x renaming of
            Nothing -> v
            Just j -> CVar j
        projectedColors :: [Ident]
        projectedColors = [x | ((x,_loc),Zero) <- envColors e]
        renaming = zip projectedColors (freshColors e)
eval e (App r s)       = app (eval e r) (eval e s)
eval e (Var i)         = snd (look i e)
eval e (Pi a b)        = VPi (eval e a) (eval e b)
-- eval e (Lam is x t)    = Ter (Lam is x t) e -- stop at lambdas
eval e (Lam x t)       = VLam $ \x' -> eval (Pair e (x,x')) t
eval e (Sigma a b)     = VSigma (eval e a) (eval e b)
eval e (SPair a b)     = VSPair (eval e a) (eval e b)
eval e (Fst a)         = fstSVal (eval e a)
eval e (Snd a)         = sndSVal (eval e a)
eval e (Where t decls) = eval (PDef [ (x,y) | (x,_,y) <- decls ] e) t
eval e (Con name ts)   = VCon name (map (eval e) ts)
eval e (Split pr alts) = Ter (Split pr alts) e
eval e (Sum pr ntss)   = Ter (Sum pr ntss) e
eval _ (Undef _)       = error "undefined (2)"
eval e (CLam x t) = clam' $ \i' -> eval (PCol e (x,i')) t
eval e (CApp r s) = capp (eval e r) (colEval e s)
eval e (CPi a) = VCPi (eval e a)
eval e (Path t xs) = VPath (eval e t) (VSimplex [(k,eval e z) | (colEval e . CVar -> CVar k,z) <- xs])

envColors :: Env -> [(Binder,CVal)]
envColors = \case
  Empty -> []
  Pair e _ -> envColors e
  PDef _ e -> envColors e
  PCol e x -> x:envColors e

freshColors :: Env -> [Color]
freshColors e = map Color (namesFrom ['ᚠ'..'ᛪ']) \\ [c | (_,CVar c) <- envColors e] 

colEval :: Env -> MCol TColor -> MCol Color
colEval e (CVar i) = snd $ lkCol i e
colEval e Infty = CVar $ head $ freshColors e
colEval _ Zero = Zero

evals :: Env -> [(Binder,Ter)] -> [(Binder,Val)]
evals env bts = [(b,eval env t) | (b,t) <- bts]

cevals :: [(Color,CVal)] -> Val -> Val
cevals [] = id
cevals ((i,j):xs) = ceval i j . cevals xs

vsim' :: [Val] -> Val
vsim' [x] = x
vsim' x = VSim x

vsim :: Val -> Val -> Val
vsim (VSim xs) (VSim ys) = vsim' (xs++ys)
vsim (VSim xs) x = vsim' (x:xs)
vsim x (VSim xs) = vsim' (x:xs)
vsim x y = vsim' [x,y]

-- substEnv :: Color -> CVal -> Env -> Env
-- substEnv i p env0 = case env0 of
--   Empty -> Empty
--   Pair env (b,v) -> Pair (re env) (b,ceval i p v)
--   PDef ds env -> PDef (map (second $ subst i p) ds) (re env)
--  where re = substEnv i p

-- second :: (t -> t2) -> (t1, t) -> (t1, t2)
-- second f (a,b) = (a, f b)
                 
-- subst :: Color -> CVal -> Ter -> Ter
-- subst i p t0 =
--   let su = subst i p
--       subs = (\j -> if i==j then p else CVar j)
--   in case t0 of
--     App a b -> App (su a) (su b)
--     Pi a b -> Pi (su a) (su b)
--     Lam is _ _ | Zero <- p, not (null is) -> error $ "should be gone: " ++ show t0
--     Lam is x b -> Lam [j | CVar j <- map subs is] x (su b)
--     Sigma a b -> Sigma (su a) (su b)
--     Fst b -> Fst (su b)
--     Snd b -> Snd (su b)
--     Where a ds -> Where (su a) [(b,su c, su d) | (b,c,d) <- ds]
--     Var x -> Var x
--     U -> U
--     Con l ts -> Con l (map su ts)
--     Split l bs -> Split l [(l',(bs',su t)) | (l',(bs',t)) <- bs]
--     Sum b ss -> Sum b $ map (second (map (second su))) ss
--     Undef l -> Undef l
--     CLam (j,b) t | CVar k <- p, k == j -> error "nope"
--                  | i == j -> t0
--                  | otherwise -> CLam (j,b) (su t)
--     CPair a b -> CPair (su a) (su b)
--     CPi b -> CPi (su b)
--     CApp a Zero -> CApp (su a) Zero
--     CApp a (CVar k) -> CApp (su a) (subs k)
--     Param a -> Param (su a)
--     Psi a -> Psi (su a)
--     Ni a b -> Ni (su a) (su b)

cevalEnv :: Color -> CVal -> Env -> Env
cevalEnv i p (Pair e (b,v)) = cevalEnv i p e `Pair` (b, ceval i p v)
cevalEnv i p (PDef d e) = PDef d $ cevalEnv i p e
cevalEnv i p (PCol e (b,p')) = PCol (cevalEnv i p e) (b, cceval i p p')
cevalEnv _i _p Empty = Empty

cceval :: Color -> CVal -> CVal -> CVal
cceval i p (CVar k) | k == i = p
cceval _ _ a = a

simplex [(_,v)] = v
simplex x = VSimplex x

ceval :: Color -> CVal -> Val -> Val
ceval i p v0 =
  let ev = ceval i p
  in case v0 of
    COLOR -> COLOR
    (VPath a borders) -> VPath (ev a) (ev borders)
    -- (VSimplexT _ _ _) -> _
    (VSimplex borders) -> simplex [(j,ev b) | (cceval i p . CVar -> (CVar j),b) <- borders]
    (VLift projections x j _t) | i == j, p == Zero -> cevals projections x
    (VLift projections x j t) -> VLift ((i,p):projections) x j t
    VU  -> VU
    Ter t env -> Ter t (cevalEnv i p env) -- add color projections!
    VPi a b -> VPi (ev a) (ev b)
    VSigma a b -> VSigma (ev a) (ev b)
    VSPair a b -> VSPair (ev a) (ev b)
    VCon x as -> VCon x (map ev as)
    VApp a b -> app (ev a) (ev b)
    VSplit a b -> VSplit (ev a) (ev b)
    VVar x -> VVar x
    VFst a -> VFst (ev a)
    VSnd a -> VSnd (ev a)
    VCApp a k -> capp (ev a) (cceval i p k)
    VCPi x -> VCPi (ev x)
    VCLam a -> VCLam (\k -> ev $ a k)
    VLam f -> VLam (ev . f)
    VSim xs -> VSim (fmap ev xs)

proj :: Color -> Val -> Val
proj i v = clam' (\j -> ceval i j v)  `capp` Zero

projs :: [Color] -> Val -> Val
projs [] = id
projs (i:is) = proj i . projs is

clam' :: (CVal -> Val) -> Val
clam' f = VCLam f -- clam k (f $ CVar k)
  -- where k = Color $ fresh (f $ CVar $ Color "__CLAM'__")
            -- FIXME: this is not good, because the fresh variable may
            -- capture some variables present in types.

clam :: Color -> Val -> Val
clam i (VCApp a (CVar i')) | i == i' = a   -- eta contraction (no need for occurs check!)
clam i a = VCLam $ \j -> ceval i j a

-- clams :: [Color] -> Val -> Val
-- clams [] t = t
-- clams (i:is) t = clam i $ clams is t

cpis :: Int -> ([CVal] -> Val) -> Val
cpis 0 t = t []
cpis n t = VCPi $ clam' $ \i -> cpis (n-1) $ \is -> t (i:is)

cpi :: (CVal -> Val) -> Val
cpi f = VCPi (VCLam f)

(<∋>) :: Functor f => f a -> (a -> b) -> f b
(<∋>) = flip fmap

capp :: Val -> CVal -> Val
capp (VSim xs) i = VSim (xs <∋> (`capp` i))
capp (VCLam f) x = f x
capp f a = VCApp f a

capps :: Val -> [CVal] -> Val
capps a [] = a
capps a (i:is) = capps (capp a i) is


-- | Decompose a value in a number of colors and zip it with a simplex.
type Simplex a = [(Color,a)]
simplexZip :: (x -> Val -> a) -> Simplex x -> Val -> Simplex a
simplexZip f s t = [(i,f si (projs (cols \\ [i]) t)) | (i,si) <- s]
  where cols = map fst s

app :: Val -> Val -> Val
app (VSimplex f) u = VSimplex (simplexZip app f u)
-- app u (VSimplex t) = VSimplex (simplexZip (flip app) t u)
app (VLam f) u = f u
-- app (Ter (Lam cs x t) e) u = eval (Pair e (x,clams cs u)) t
app (Ter (Split _ nvs) e) (VCon name us) = case lookup name nvs of
    Just (xs,t) -> eval (upds e (zip xs us)) t
    Nothing -> error $ "app: Split with insufficient arguments; " ++
                        "missing case for " ++ name
app u@(Ter (Split _ _) _) v | isNeutral v = VSplit u v -- v should be neutral
                            | otherwise   = error $ "app: VSplit " ++ show v
                                                  ++ " is not neutral"
app r s | isNeutral r = VApp r s -- r should be neutral
        | otherwise   = error $ "app: VApp " ++ show r ++ " is not neutral"

fstSVal, sndSVal :: Val -> Val
fstSVal (VSPair a _)    = a
fstSVal u | isNeutral u = VFst u
          | otherwise   = error $ show u ++ " should be neutral"
sndSVal (VSPair _ b)    = b
sndSVal u | isNeutral u = VSnd u
          | otherwise   = error $ show u ++ " should be neutral"

convs :: Int -> [Val] -> [Val] -> Err
convs k a b = mconcat $ zipWith (conv k) a b

equal :: (Show a, Eq a) => a -> a -> Err
equal a b | a == b = NoErr
          | otherwise = different a b

different :: (Show a2, Show a1) => a1 -> a2 -> Err
different a b = Err $ show a ++ " /= " ++ show b

data Err = Err String | NoErr deriving Show

instance Semigroup Err where
  NoErr <> x = x
  Err x <> _ = Err x

instance Monoid Err where
  mempty = NoErr

conv :: Int -> Val -> Val -> Err
conv k (VSim xs) y = anyOf [conv k x y | x <- xs]
conv k y (VSim xs) = anyOf [conv k y x | x <- xs]
conv _ VU VU = NoErr
conv k (VLam f) t = conv (k+1) (f v) (t `app` v)
  where v = mkVar k
conv k t (VLam f) = conv (k+1) (f v) (t `app` v)
  where v = mkVar k
conv k (VCPi f) (VCPi f') = conv k f f'
conv k (VCLam f) t = conv (k+1) (f c) (capp t c)
  where c = mkCol k
conv k t (VCLam f) = conv k (VCLam f) t
conv k (VCApp a b) (VCApp a' b') = conv k a a' <> equal b b'
conv k (VSimplex x) y = mconcat $ map snd $ simplexZip (conv k) x y
conv k y (VSimplex x) = mconcat $ map snd $ simplexZip (flip (conv k)) x y
-- conv k (Ter (Lam cs x u) e) (Ter (Lam cs' x' u') e') = do
--   let v = mkVar k
--   cs `equal` cs' <> conv (k+1) (eval (Pair e (x,v)) u) (eval (Pair e' (x',v)) u')
-- conv k (Ter (Lam is x u) e) u' = do
--   let v = mkVar k
--   conv (k+1) (eval (Pair e (x,clams is v)) u) (app u' v)
-- conv k u' (Ter (Lam is x u) e) = do
--   let v = mkVar k
--   conv (k+1) (app u' v) (eval (Pair e (x,clams is v)) u)
conv k (Ter (Split p _) e) (Ter (Split p' _) e') =
  (p `equal` p') <> convEnv k e e'
conv k (Ter (Sum p _) e)   (Ter (Sum p' _) e') =
  (p `equal` p') <> convEnv k e e'
conv k (Ter (Undef p) e) (Ter (Undef p') e') =
  (p `equal` p') <> convEnv k e e'
conv k (VPi u v) (VPi u' v') = do
  let w = mkVar k
  conv k u u' <> conv (k+1) (app v w) (app v' w)
conv k (VSigma u v) (VSigma u' v') = do
  let w = mkVar k
  conv k u u' <> conv (k+1) (app v w) (app v' w)
conv k (VFst u) (VFst u') = conv k u u'
conv k (VSnd u) (VSnd u') = conv k u u'
conv k (VCon c us) (VCon c' us') =
  (c `equal` c') <> mconcat (zipWith (conv k) us us')
conv k (VSPair u v) (VSPair u' v') = conv k u u' <> conv k v v'
conv k (VSPair u v) w              =
  conv k u (fstSVal w) <> conv k v (sndSVal w)
conv k w            (VSPair u v)   =
  conv k (fstSVal w) u <> conv k (sndSVal w) v
conv k (VApp u v)   (VApp u' v')   = conv k u u' <> conv k v v'
conv k (VSplit u v) (VSplit u' v') = conv k u u' <> conv k v v'
conv _ (VVar x)     (VVar x')      = x `equal` x'
conv _ x              x'           = different x x'

convEnv :: Int -> Env -> Env -> Err
convEnv k e e' = mconcat $ zipWith (conv k) (valOfEnv e) (valOfEnv e')

subset :: Eq a => [a] -> [a] -> Bool
subset x y = null (x \\ y)

sub :: Int -> [Val] -> Val -> Val -> Err
sub k value (VPath p x) q = sub k (x:value) p q
sub k value q (VPath p x) = sub k value q p <> anyOf [conv k x v | v <- value]
sub k x (VCPi f) (VCPi f') = sub (k+1) ((`capp` v) <$> x) (f `capp` v) (f' `capp` v)
  where v = mkCol k
sub k _ subt super = conv k subt super

orElse :: Err -> Err -> Err
orElse NoErr _ = NoErr
orElse _ NoErr = NoErr
orElse (Err x) (Err y) = Err (x <> " and " <> y)

anyOf :: [Err] -> Err
anyOf [] = error "anyOf: at least one choice is necessary!"
anyOf x = foldr1 orElse x


-- ttt :: Val
-- ttt = cpi $ \(CVar i) -> cpi $ \(CVar j) -> VPath (VVar "X2") [(i,app (VVar "X3") (VVar "X8")),(j,app (VVar "X4") (VVar "X8"))]

-- uuu :: Val
-- uuu = VPath (VVar "X2") [(Color "i",app (VVar "X3") (VVar "X8")),(Color "j",app (VVar "X4") (VVar "X8"))]

-- -- >>> ttt
-- -- PI <α> PI <β> ID(X2) [(α/X3 X8)(β/X4 X8)]

-- -- >>> sub 0 [] ttt ttt
-- -- NoErr
