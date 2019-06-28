{-# LANGUAGE PatternSynonyms, FlexibleContexts, RecordWildCards #-}
module TypeChecker where

import Data.Function
import Data.List
import Data.Monoid hiding (Sum)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Except
import Control.Monad.Trans.Reader

import CTT
import Eval

-- Type checking monad
type Typing a = ReaderT TEnv (ExceptT String IO) a

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , env     :: Env
                 , ctxt    :: Ctxt
                 , errCtx  :: [String]
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 }
  deriving (Show)

reAbsCtxtOnCol :: TColor -> Color -> Ctxt -> Ctxt
reAbsCtxtOnCol _ _ [] = []
reAbsCtxtOnCol x i (((x',x'loc),COLOR):ctx)
  | x == x' = ctx
  | otherwise = ((x',x'loc),COLOR):reAbsCtxtOnCol x i ctx
reAbsCtxtOnCol x i ((b,v):ctx) = (b, VCPi $ cabs v):reAbsCtxtOnCol x i ctx
  where cabs body = clam i body

reAbsCtxt :: TColor -> Color -> Ctxt -> Ctxt
reAbsCtxt i j = reAbsCtxtOnCol i j

possiblyReAbsAll :: CTer -> CVal -> TEnv -> TEnv
possiblyReAbsAll (CVar x) (CVar i) e = reAbsAll x i e
possiblyReAbsAll _ _ e = e

reAbsAll :: TColor -> Color -> TEnv -> TEnv
reAbsAll x i e = e {env = reAbsWholeEnvOnCol x i (env e),
                    ctxt = reAbsCtxt x i (ctxt e)}

showCtxt :: Show a => [(([Char], t), a)] -> [Char]
showCtxt ctx = intercalate ", \n" $ reverse $ [i ++ " : " ++ show v | ((i,_),v) <- ctx]

logg :: String -> Typing a -> Typing a
logg x = local (\e -> e {errCtx = x:errCtx e})

oops :: String -> Typing a
oops msg = do
  TEnv {..} <- ask
  throwError ("In:\n" ++ concatMap (++ ":\n") (reverse errCtx) ++ msg ++ "\n in environment" ++ show env ++ "\n in context\n" ++ showCtxt ctxt )

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv 0 Empty [] [] True
silentEnv  = TEnv 0 Empty [] [] False

addCol :: Binder -> CVal -> TEnv -> TEnv
addCol x p@(CVar _) (TEnv k rho gam ex v) = TEnv (k+1) (PCol rho (x,p)) ((x,COLOR):gam) ex v
addCol _ _ _ = error "typechecker can't add Zero (because of Lift checking)"

addTypeVal :: (Binder, Val) -> TEnv -> TEnv
addTypeVal p@(x,_) (TEnv k rho gam ex v) =
  TEnv (k+1) (Pair rho (x,mkVar k)) (p:gam) ex v

addType :: (Binder,Ter) -> TEnv -> Typing TEnv
addType (x,a) tenv@(TEnv _ rho _ _ _) = return $ addTypeVal (x,eval rho a) tenv

addC :: Ctxt -> (Tele,Env) -> [(Binder,Val)] -> Typing Ctxt
addC gam _             []          = return gam
addC gam ((y,a):as,nu) ((x,u):xus) = 
  addC ((x,eval nu a):gam) (as,Pair nu (y,u)) xus
addC _ ([], _) (_:_) = error "addC: panic: impossible case"

addBranch :: [(Binder,Val)] -> (Tele,Env) -> TEnv -> Typing TEnv
addBranch nvs (tele,env) (TEnv k rho gam ex v) = do
  e <- addC gam (tele,env) nvs
  return $ TEnv (k + length nvs) (upds rho nvs) e ex v

addDecls :: Decls -> TEnv -> Typing TEnv
addDecls d (TEnv k rho gam ex v) = do
  let rho1 = PDef [ (x,y) | (x,_,y) <- d ] rho
      es' = evals rho1 (declDefs d)
  gam' <- addC gam (declTele d,rho) es'
  return $ TEnv k rho1 gam' ex v

addTele :: Tele -> TEnv -> Typing TEnv
addTele xas lenv = foldM (flip addType) lenv xas

trace :: String -> Typing ()
trace s = do
  b <- verbose <$> ask
  when b $ liftIO (putStrLn s)

runTyping :: TEnv -> Typing a -> IO (Either String a)
runTyping env t = runExceptT $ runReaderT t env

-- Used in the interaction loop
runDecls :: TEnv -> Decls -> IO (Either String TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  addDecls d tenv

runDeclss :: TEnv -> [Decls] -> IO (Maybe String,TEnv)
runDeclss tenv []         = return (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping lenv (snd <$> checkInfer e)

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ cas) r) = case getIdent c cas of
  Just as -> return (as,r)
  Nothing -> oops ("getLblType " ++ show c)
getLblType c u = oops ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Useful monadic versions of functions:
localM :: (TEnv -> Typing TEnv) -> Typing a -> Typing a
localM f r = do
  e <- ask
  a <- f e
  local (const a) r

getFresh :: Typing Val
getFresh = mkVar <$> index <$> ask

getFreshCol :: Typing CVal
getFreshCol = mkCol <$> index <$> ask

checkDecls :: Decls -> Typing ()
checkDecls d = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking: " ++ unwords idents)
  checkTele tele
  rho <- asks env
  localM (addTele tele) $ checks (tele,rho) ters

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  _ <- inferType a
  localM (addType (x,a)) $ checkTele xas

checkLogg :: Val -> Ter -> Typing Val
checkLogg v t = logg ("Checking that " ++ show t ++ " has type " ++ show v) $ check v t

check :: Val -> Ter -> Typing Val
check a t = logg ("Extra Checking that " ++ show t ++ " has type " ++ show a) $
 let dflt = eval' t
 in case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
    dflt
  (_,CApp u@(CLam _ _) c) -> do
    -- we prefer to infer type for CApp, because then we also get a
    -- (possibly precise) value.  however, if we have a lambda inside
    -- then we wont be able to infer. But, we're still able to check
    -- and so we proceed here
    c' <- colorEval c
    case (c,c') of
      (CVar i,CVar i') -> local (reAbsAll i i') $ do
        -- ctx <- asks ctxt
        -- trace ("after reabs " <> show (i,i') <> "\n, context became \n" <> showCtxt ctx)
        checkLogg (cpi $ \j -> ceval i' j a) u
      _ -> logg ("in capp, checking that term " ++ show t ++ " has type " ++ show a) $ do
          (t',v) <- checkInfer t
          checkSub "inferred type" [t'] v a -- if not a variable, fall back to plain inference
          return t'
  (VU,Sum _ bs) -> do
    sequence_ [checkTele as | (_,as) <- bs]
    dflt
  (VPi (Ter (Sum _ cas) nu) f,Split _ ces) -> do
    let cas' = sortBy (compare `on` fst . fst) cas
        ces' = sortBy (compare `on` fst) ces
    _ <- if map (fst . fst) cas' == map fst ces'
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces' cas' ]
       else oops "case branches does not match the data type"
    dflt
  (VPi aa f,Lam x tt)  -> do
    var <- getFresh
    _ <- local (addTypeVal (x,aa)) $ check (app f var) tt
    dflt
  (VPath (VPi aa f) borders,Lam x tt) -> do
    var <- getFresh
    _ <- local (addTypeVal (x,aa)) $ check (VPath (app f var) (borders `app` var)) tt
    dflt
  (VSigma aa f, SPair t1 t2) -> do
    v <- check aa t1
    v2 <- check (app f v) t2
    return (VSPair v v2)
  (VCPi f, CLam x b) -> do
    var <- getFreshCol
    _ <- local (addCol x var) $ check (capp f var) b
    dflt
  (_,Where e d) -> do
    checkDecls d
    localM (addDecls d) $ check a e
  (_,Undef _) -> error "undefined (3)"
  _ -> do
    logg ("checking that term " ++ show t ++ " has type " ++ show a) $ do
       (x,v) <- checkInfer t
       checkSub "inferred type" [x] v a
       return x


arrs :: [Val] -> Val -> Val
arrs [] t = t
arrs (a:as) t = VPi a $ VLam $ \_ -> arrs as t

-- checkNumber :: Show a => [a] -> Typing ()
-- checkNumber as = do
--   when (length as /= numberOfFaces) $ do
--     throwError $ show as ++ " should be a tuple of " ++ show numberOfFaces

colorEval :: CTer -> Typing CVal
colorEval c = do
  e <- asks env
  return $ colEval e c

eval' :: Ter -> Typing Val
eval' t = do
  e <- asks env
  return $ eval e t

checkSub :: [Char] -> [Val] -> Val -> Val -> ReaderT TEnv (ExceptT String IO) ()
checkSub msg value subtyp super = do
    k <- index <$> ask
    case sub k value subtyp super of
      NoErr -> return ()
      Err err -> do
      oops $ msg ++ " check sub: \n  " ++ show value ++ "value \n  "++ show subtyp ++ " ⊄ " ++ show super ++ "\n because  " ++ err

checkConv :: [Char] -> Val -> Val -> ReaderT TEnv (ExceptT String IO) ()
checkConv msg subtyp super = do
    k <- index <$> ask
    case conv k subtyp super of
      NoErr -> return ()
      Err err -> do
      oops $ msg ++ " check conv: \n  " ++ show subtyp ++ " ⊄ " ++ show super ++ "\n because  " ++ err

checkBranch :: (Tele,Env) -> Val -> Brc -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k   <- asks index
  -- env <- asks env
  let l  = length xas
      us = map mkVar [k..k+l-1]
  _ <- localM (addBranch (zip xs us) (xas,nu)) $ check (app f (VCon c us)) e
  return ()

inferTypeEval :: Ter -> Typing (Val,Val)
inferTypeEval t = do
  (t',a) <- checkInfer t
  case a of
   VU -> return (t',a)
   VPath VU _ -> return (t',a)
   _ -> oops $ show t ++ " is not a type, but " ++ show a

colVarEval :: TColor -> Typing Color
colVarEval i = do
  rho <- asks env
  -- in the typechecker we NEVER put Zero in the color environment.
  let CVar i' = colEval rho (CVar i)
  return i'

-- Infer a value's type and return its value AND all the values that it also is known to be thanks to its type.
checkInfer :: Ter -> Typing (Val,Val)
checkInfer e = do
  x@(e',t) <- checkInfer' e
  r <- case t of
    (VPath _ border) -> return (vRemBorder e' border,t)
    _ -> return x
  -- trace ("Inferred: " <> show e <> " is " <> show r)
  return r

inferType :: Ter -> Typing Val
inferType a = do
  (_,t) <- inferTypeEval a
  return t

-- choiceA  :: (Foldable f, Alternative a) => f (a x) -> a x
-- choiceA :: Alternative m => [x] -> (x -> m y) -> m y
-- choiceA xs f = foldr (<|>) empty (map f xs)

checkInfer' :: Ter -> Typing (Val,Val)
checkInfer' e =
  let typ = do
        rho <- asks env
        return (eval rho e, VU)
  in case e of
{-
   Γ ⊢ A : U
   Γ ⊢ t : A[0/i]
---------------------
   Γ ⊢ t ^i A : A
-}
  Lift t i a -> do
    (a',_) <- inferTypeEval a
    i' <- colVarEval i
    t' <- check (proj i' a') t
    return (Eval.lift [] t' i' a', a')
  Path a ixs -> do
    a' <- check VU a
    ixs' <- forM ixs $ \(i,x) -> do
      i' <- colVarEval i
      x' <- check (proj i' a') x
      return (i',x')
    return (VPath a' (VSimplex ixs'),VU)
  CPi (CLam x t) -> do
    var <- getFreshCol
    _ <- local (addCol x var) $ inferType t
    typ
  CLam i t -> do -- additional rule to infer CLam
    var@(CVar v) <- getFreshCol
    (t',a) <- local (addCol i var) $ checkInfer t
    return (clam' $ \i' -> ceval v i' t', cpi $ \i' -> ceval v i' a)
  Pi a (Lam x b) -> do
    _ <- inferType a
    _ <- localM (addType (x,a)) $ inferType b
    typ
  Sigma a (Lam x b) -> do
    _ <- inferType a
    _ <- localM (addType (x,a)) $ inferType b
    typ
  U -> typ
  Var n -> do
    n' <- eval' (Var n)
    gam <- ctxt <$> ask
    case getIdent n gam of
      Just v  -> return (n',v)
      Nothing -> oops $ show n ++ " is not declared!"
  App t u -> do
    (t',c) <- checkInfer t
    case c of
      VPi a f -> do
        v <- check a u
        -- trace ("in app: " ++ show v ++ " :: " ++ show a)
        return $ (app t' v, app f v)
      _       -> oops $ show t' ++ " is not a product"
  Fst t -> do
    (t',c) <- checkInfer t
    case c of
      VSigma a _f -> return (fstSVal t',a)
      _ -> oops $ show c ++ " is not a sigma-type"
  Snd t -> do
    (v,c) <- checkInfer t
    case c of
      VSigma _a f -> do
        return $ (sndSVal v, app f (fstSVal v))
      _          -> oops $ show c ++ " is not a sigma-type"
  CApp t u -> do
    u' <- colorEval u
    (t',c) <- local (possiblyReAbsAll u u') $ do
      -- ctx <- asks ctxt
      -- trace ("after reabs " <> show (u,u') <> "\n, context became \n" <> showCtxt ctx)
      (checkInfer t)
    case c of
      VCPi f -> do return $ (capp t' u', capp f u')
      _          -> oops $ show t ++ " is not a family (1), but " ++ show c
  Where t d -> do
    checkDecls d
    localM (addDecls d) $ checkInfer t
  _ -> oops ("cannot infer the type of " ++ show e)

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  let v = eval nu a
  v' <- check v e
  checks (xas,Pair nu (x,v')) es
checks _              _      = oops "checks"

