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
runInfer lenv e = runTyping lenv (checkInfer e)

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

checkLogg :: Val -> Ter -> Typing ()
checkLogg v t = logg ("Checking that " ++ show t ++ " has type " ++ show v) $ check v t

check :: Val -> Ter -> Typing ()
check a t = logg ("Extra Checking that " ++ show t ++ " has type " ++ show a) $
  case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (_,CApp u c) -> do
    c' <- colorEval c
    case (c,c') of
      (CVar i,CVar i') -> local (reAbsAll i i') $ do
        -- ctx <- asks ctxt
        -- trace ("after reabs " <> show (i,i') <> "\n, context became \n" <> showCtxt ctx)
        checkLogg (cpi $ \j -> ceval i' j a) u
      _ -> logg ("in capp, checking that term " ++ show t ++ " has type " ++ show a) $ do
          v <- checkInfer t
          checkSub "inferred type" [] v a -- if not a variable, fall back to plain inference
  (VU,Sum _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (VPi (Ter (Sum _ cas) nu) f,Split _ ces) -> do
    let cas' = sortBy (compare `on` fst . fst) cas
        ces' = sortBy (compare `on` fst) ces
    if map (fst . fst) cas' == map fst ces'
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces' cas' ]
       else oops "case branches does not match the data type"
  (VPi aa f,Lam x tt)  -> do
    var <- getFresh
    local (addTypeVal (x,aa)) $ check (app f var) tt
  (VPath (VPi aa f) borders,Lam x tt)  -> do
    var <- getFresh
    local (addTypeVal (x,aa)) $ check (VPath (app f var) [(i,b `app` var) | (i,b) <- borders]) tt
  (VSigma aa f, SPair t1 t2) -> do
    v <- checkEval aa t1
    check (app f v) t2
  (VCPi f, CLam x b) -> do
    var <- getFreshCol
    local (addCol x var) $ check (capp f var) b
  (_,Where e d) -> do
    checkDecls d
    localM (addDecls d) $ check a e
  (_,Undef _) -> return ()
  _ -> do
    logg ("checking that term " ++ show t ++ " has type " ++ show a) $ do
       v <- checkInfer t
       x <- eval <$> asks env <*> pure t
       checkSub "inferred type" [x] v a


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
  
checkEval :: Val -> Ter -> Typing Val
checkEval a t = do
  checkLogg a t
  eval' t

eval' :: Ter -> Typing Val
eval' t = do
  e <- asks env
  return $ eval e t

-- checkConvs :: String -> [Val] -> [Val] -> Typing ()
-- checkConvs msg a v = sequence_ [checkConv msg a' v' | (a',v') <- zip a v]

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
  localM (addBranch (zip xs us) (xas,nu)) $ check (app f (VCon c us)) e

inferType :: Ter -> Typing Val
inferType t = do
  a <- checkInfer t
  case a of
   VU -> return a
   VPath VU _ -> return a
   _ -> oops $ show t ++ " is not a type, but " ++ show a

colVarEval :: TColor -> Typing Color
colVarEval i = do
  rho <- asks env
  -- in the typechecker we NEVER put Zero in the color environment.
  let CVar i' = colEval rho (CVar i)
  return i'

checkInfer :: Ter -> Typing Val
checkInfer e = do
  x <- checkInfer' e
  trace ("Inferred: " <> show e <> " has type " <> show x)
  return x

-- inferTypeEval a = do
--   t <- inferType a
--   a' <- eval' a
--   case t of
--     VPath _ borders -> return [borders,a]
--     _ -> return a

checkInfer' :: Ter -> Typing Val
checkInfer' e = case e of
{-

   Γ ⊢ A : U
   Γ ⊢ t : A[0/i]
---------------------
   Γ ⊢ t ^i A : A

-}
  Lift t i a -> do
    _ <- inferType a
    a' <- eval' a
    i' <- colVarEval i
    check (proj i' a') t
    return a'
  Path a ixs -> do
    a' <- checkEval VU a
    forM_ ixs $ \(i,x) -> do
      i' <- colVarEval i
      check (proj i' a') x
    return VU
  CPi (CLam x t) -> do
    var <- getFreshCol
    _ <- local (addCol x var) $ inferType t
    return VU
  CLam i t -> do -- additional rule to infer CLam
    var@(CVar v) <- getFreshCol
    a <- local (addCol i var) $ checkInfer t
    return (cpi $ \i' -> ceval v i' a)
  Pi a (Lam x b) -> do
    _ <- inferType a
    localM (addType (x,a)) $ inferType b
  Sigma a (Lam x b) -> do
    _ <- inferType a
    localM (addType (x,a)) $ inferType b
  U -> return VU                 -- U : U
  Var n -> do
    gam <- ctxt <$> ask
    case getIdent n gam of
      Just v  -> return v
      Nothing -> oops $ show n ++ " is not declared!"
  App t u -> do
    c <- checkInfer t
    case c of
      VPi a f -> do
        checkLogg a u
        rho <- asks env
        let v = eval rho u
        return $ app f v
      _       -> oops $ show c ++ " is not a product"
  Fst t -> do
    c <- checkInfer t
    case c of
      VSigma a _f -> return a
      _          -> oops $ show c ++ " is not a sigma-type"
  Snd t -> do
    c <- checkInfer t
    case c of
      VSigma _a f -> do
        rho <- asks env
        let v = eval rho t
        return $ app f (fstSVal v)
      _          -> oops $ show c ++ " is not a sigma-type"
  CApp t u -> do
    u' <- colorEval u
    c <- local (possiblyReAbsAll u u') $ do
      -- ctx <- asks ctxt
      -- trace ("after reabs " <> show (u,u') <> "\n, context became \n" <> showCtxt ctx)
      (checkInfer t)
    case c of
      VCPi f -> do return $ (capp f u')
      _          -> oops $ show t ++ " is not a family (1), but " ++ show c
  Where t d -> do
    checkDecls d
    localM (addDecls d) $ checkInfer t
  _ -> oops ("cannot infer the type of " ++ show e)

extractFun :: Int -> Val -> Typing ([Val],Val)
extractFun 0 a = return ([],a)
extractFun n (VPi a f) = do
  (as,b) <- extractFun (n-1) (f `app` VVar "extractFun")
  return (a:as,b)

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  let v = eval nu a
  check v e
  rho <- asks env
  let v' = eval rho e
  checks (xas,Pair nu (x,v')) es
checks _              _      = oops "checks"

-- Not used since we have U : U
--
-- (=?=) :: Typing Ter -> Ter -> Typing ()
-- m =?= s2 = do
--   s1 <- m
--   unless (s1 == s2) $ oops (show s1 ++ " =/= " ++ show s2)
--
-- checkTs :: [(String,Ter)] -> Typing ()
-- checkTs [] = return ()
-- checkTs ((x,a):xas) = do
--   checkType a
--   local (addType (x,a)) (checkTs xas)
--
-- checkType :: Ter -> Typing ()
-- checkType t = case t of
--   U              -> return ()
--   Pi a (Lam x b) -> do
--     checkType a
--     local (addType (x,a)) (checkType b)
--   _ -> checkInfer t =?= U
