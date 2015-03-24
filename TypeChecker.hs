module TypeChecker where

import Data.Either
import Data.Function
import Data.List
import Data.Maybe
import Data.Map (Map,(!))
import qualified Data.Map as Map
import Data.Monoid hiding (Sum)
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Trans.Reader
import Control.Monad.Error (throwError)
import Control.Applicative

import Connections
import CTT
import Eval

-- Type checking monad
type Typing a = ReaderT TEnv (ErrorT String IO) a

-- Environment for type checker
data TEnv = TEnv { index   :: Int   -- for de Bruijn levels
                 , env     :: Env
                 , verbose :: Bool  -- Should it be verbose and print
                                    -- what it typechecks?
                 }
  deriving (Eq,Show)

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv 0 Empty True
silentEnv  = TEnv 0 Empty False

addTypeVal :: (Ident,Val) -> TEnv -> TEnv
addTypeVal (x,a) (TEnv k rho v) =
  TEnv (k+1) (Upd rho (x,mkVar k a)) v

addSub :: (Name,Formula) -> TEnv -> TEnv
addSub iphi (TEnv k rho v) = TEnv k (Sub rho iphi) v

addType :: (Ident,Ter) -> TEnv -> Typing TEnv
addType (x,a) tenv@(TEnv _ rho _) = return $ addTypeVal (x,eval rho a) tenv

addBranch :: [(Ident,Val)] -> (Tele,Env) -> TEnv -> TEnv
addBranch nvs (tele,env) (TEnv k rho v) =
  TEnv (k + length nvs) (upds rho nvs) v

addDecls :: [Decl] -> TEnv -> TEnv
addDecls d (TEnv k rho v) = TEnv k (Def d rho) v

addTele :: Tele -> TEnv -> Typing TEnv
addTele xas lenv = foldM (flip addType) lenv xas

faceEnv :: Face -> TEnv -> TEnv
faceEnv alpha tenv = tenv{env=env tenv `face` alpha}

trace :: String -> Typing ()
trace s = do
  b <- verbose <$> ask
  when b $ liftIO (putStrLn s)

runTyping :: TEnv -> Typing a -> IO (Either String a)
runTyping env t = runErrorT $ runReaderT t env

-- Used in the interaction loop
runDecls :: TEnv -> [Decl] -> IO (Either String TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  return $ addDecls d tenv

runDeclss :: TEnv -> [[Decl]] -> IO (Maybe String,TEnv)
runDeclss tenv []         = return (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping lenv (infer e)

-- Extract the type of a label as a closure
getLblType :: String -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ _ cas) r) = case lookup c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType: " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Useful monadic versions of functions:
localM :: (TEnv -> Typing TEnv) -> Typing a -> Typing a
localM f r = do
  e <- ask
  a <- f e
  local (const a) r

getFresh :: Val -> Typing Val
getFresh a = do
    k <- index <$> ask
    e <- asks env
    return $ mkVar k a

checkDecls :: [Decl] -> Typing ()
checkDecls d = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking: " ++ unwords idents)
  checkTele tele
  rho <- asks env
  localM (addTele tele) $ checks (tele,rho) ters

checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check VU a
  localM (addType (x,a)) $ checkTele xas

checkFam :: Ter -> Typing ()
checkFam (Lam x a b) = do
  check VU a
  localM (addType (x,a)) $ check VU b
checkFam _ = throwError "checkFam"

constPath :: Val -> Val
constPath v = VPath (Name "_") v

-- Check that t has type a
check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Pi f) -> checkFam f
  (VU,Sigma f) -> checkFam f
  (VU,Sum _ _ bs) -> sequence_ [checkTele as | (_,as) <- bs]
  (VPi (Ter (Sum _ _ cas) nu) f,Split _ f' ces) -> do
    checkFam f'
    k <- asks index
    rho <- asks env
    unless (conv k f (eval rho f')) $ throwError "check: split annotations"
    let cas' = sortBy (compare `on` fst) cas
        ces' = sortBy (compare `on` fst) ces
    if map fst cas' == map fst ces'
       then sequence_ [ checkBranch (as,nu) f brc
                      | (brc, (_,as)) <- zip ces' cas' ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x a' t)  -> do
    check VU a'
    k <- asks index
    rho <- asks env
    unless (conv k a (eval rho a')) $ throwError "check: lam types don't match"
    var <- getFresh a
    local (addTypeVal (x,a)) $ check (app f var) t
  (VSigma a f, Pair t1 t2) -> do
    check a t1
    e <- asks env
    let v = eval e t1
    check (app f v) t2
  (_,Where e d) -> do
    checkDecls d
    local (addDecls d) $ check a e
  (_,Undef _) -> return ()
  (VU,IdP a e0 e1) -> do
    (a0,a1) <- checkPath (constPath VU) a
    check a0 e0
    check a1 e1
  (VIdP p a0 a1,Path i e) -> do
    rho <- asks env
    k   <- asks index
    when (i `elem` support rho)
      (throwError (show i ++ " is already declared"))
    local (addSub (i,Atom i)) $ check (p @@ i) e
    let u0 = eval (Sub rho (i,Dir 0)) e
        u1 = eval (Sub rho (i,Dir 1)) e
    unless (conv k a0 u0 && conv k a1 u1) $
      throwError $ "path endpoints don't match " ++ show e ++
                   " \nu0 = " ++ show u0 ++ " \nu1 = " ++ show u1 ++
                   " \na0 = " ++ show a0 ++ " \na1 = " ++ show a1 ++
                   " \np = " ++ show p
  (VU,Glue a ts) -> do
    check VU a
    rho <- asks env
    checkGlue (eval rho a) ts
  (VGlue va ts,GlueElem u us) -> do
    check va u
    rho <- asks env
    let vu = eval rho u
    checkGlueElem vu ts us
  _ -> do
    v <- infer t
    k <- index <$> ask
    unless (conv k v a) $
      throwError $ "check conv: " ++ show v ++ " /= " ++ show a

checkGlueElem :: Val -> System Val -> System Ter -> Typing ()
checkGlueElem vu ts us = do
  unless (Map.keys ts == Map.keys us)
    (throwError ("Keys don't match in " ++ show ts ++ " and " ++ show us))
  rho <- asks env
  k <- asks index
  sequence_ $ Map.elems $ Map.intersectionWithKey
    (\alpha vt u -> check (hisoDom vt) u) ts us
    
  let vus = evalSystem rho us
  sequence_ $ Map.elems $ Map.intersectionWithKey
    (\alpha vt vAlpha -> do
       unless (conv k (app (hisoFun vt) vAlpha) (vu `face` alpha))
          (throwError $ "Image of glueElem component " ++ show vAlpha ++
                        " doesn't match " ++ show vu)) ts vus
  unless (isCompSystem k vus)
    (throwError $ "Incompatible system " ++ show vus)

checkGlue :: Val -> System Ter -> Typing ()
checkGlue va ts = do
  sequence_ $ Map.elems $
    Map.mapWithKey (\alpha tAlpha -> checkIso (va `face` alpha) tAlpha) ts
  k <- asks index
  rho <- asks env
  unless (isCompSystem k (evalSystem rho ts))
    (throwError ("Incompatible system " ++ show ts))

-- An hiso for a type a is a five-tuple: (b,f,g,r,s)   where
--  b : U
--  f : b -> a
--  g : a -> b
--  s : forall (y : a), f (g y) = y
--  t : forall (x : b), g (f x) = x
checkIso :: Val -> Ter -> Typing ()
checkIso va (Pair b (Pair f (Pair g (Pair s t)))) = do
  check VU b
  rho <- asks env
  let vb = eval rho b
  check (mkFun vb va) f
  check (mkFun va vb) g
  let vf = eval rho f
      vg = eval rho g
  check (mkSection va vb vf vg) s
  check (mkSection vb va vg vf) t

mkFun :: Val -> Val -> Val
mkFun va vb = VPi va (eval rho (Lam "_" (Var "a") (Var "b")))
  where rho = Upd (Upd Empty ("a",va)) ("b",vb)

mkSection :: Val -> Val -> Val -> Val -> Val
mkSection va _ vf vg =
  VPi va (eval rho (Lam "y" a (IdP (Path (Name "_") a) (App f (App g y)) y)))
  where [a,y,f,g] = map Var ["a","y","f","g"]
        rho = Upd (Upd (Upd Empty ("a",va)) ("f",vf)) ("g",vg)
  
checkBranch :: (Tele,Env) -> Val -> Branch -> Typing ()
checkBranch (xas,nu) f (c,(xs,e)) = do
  k   <- asks index
  env <- asks env
  let us = mkVars k xas nu
  local (addBranch (zip xs us) (xas,nu)) $ check (app f (VCon c us)) e

mkVars k [] _ = []
mkVars k ((x,a):xas) nu =
  let w = mkVar k (eval nu a)
  in w : mkVars (k+1) xas (Upd nu (x,w))

checkFormula :: Formula -> Typing ()
checkFormula phi = do
  rho <- asks env
  let dom = domainEnv rho
  if all (\x -> x `elem` dom) (support phi)
    then return ()
    else throwError ("checkFormula: " ++ show phi)

-- infer the type of e
infer :: Ter -> Typing Val
infer e = case e of
  U     -> return VU  -- U : U
  Var n -> do
    rho <- env <$> ask
    return $ lookType n rho
  App t u -> do
    c <- infer t
    case c of
      VPi a f -> do
        check a u
        rho <- asks env
        let v = eval rho u
        return $ app f v
      _       -> throwError $ show c ++ " is not a product"
  Fst t -> do
    c <- infer t
    case c of
      VSigma a f -> return a
      _          -> throwError $ show c ++ " is not a sigma-type"
  Snd t -> do
    c <- infer t
    case c of
      VSigma a f -> do
        e <- asks env
        let v = eval e t
        return $ app f (fstVal v)
      _          -> throwError $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDecls d
    local (addDecls d) $ infer t
  AppFormula e phi -> do
    checkFormula phi
    t <- infer e
    case t of
      VIdP a _ _ -> return $ a @@ phi
      _ -> throwError (show e ++ " is not a path")
  Trans p t -> do
    (a0,a1) <- checkPath (constPath VU) p
    check a0 t
    return a1
  Comp a t0 ts -> do
    check VU a
    rho <- asks env
    let va = eval rho a
    check va t0

    -- check rho alpha |- t_alpha : a alpha
    sequence $ Map.elems $
      Map.mapWithKey (\alpha talpha ->
                       local (faceEnv alpha) $ do
                         rhoAlpha <- asks env
                         (a0,_) <- checkPath (constPath (va `face` alpha)) talpha
                         k <- asks index
                         unless (conv k a0 (eval rhoAlpha t0))
                           (throwError ("incompatible system with " ++ show t0))
                     ) ts

    -- check that the system is compatible
    k <- asks index
    unless (isCompSystem k (evalSystem rho ts))
      (throwError ("Incompatible system " ++ show ts))
    return va
  _ -> throwError ("infer " ++ show e)

-- Check that a term is a path and output the source and target
checkPath :: Val -> Ter -> Typing (Val,Val)
checkPath v (Path i a) = do
  rho <- asks env
  when (i `elem` support rho)
    (throwError $ show i ++ " is already declared")
  local (addSub (i,Atom i)) $ check (v @@ i) a
  return (eval (Sub rho (i,Dir 0)) a,eval (Sub rho (i,Dir 1)) a)
checkPath v t = do
  vt <- infer t
  k  <- asks index
  case vt of
    VIdP a a0 a1 -> do
      unless (conv k a v) (throwError "checkPath")
      return (a0,a1)
    _ -> throwError "checkPath"

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  let v = eval nu a
  check v e
  rho <- asks env
  let v' = eval rho e
  checks (xas,Upd nu (x,v')) es
checks _              _      = throwError "checks"

-- Not used since we have U : U
--
-- (=?=) :: Typing Ter -> Ter -> Typing ()
-- m =?= s2 = do
--   s1 <- m
--   unless (s1 == s2) $ throwError (show s1 ++ " =/= " ++ show s2)
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
--   _ -> infer t =?= U
