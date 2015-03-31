{-# LANGUAGE TupleSections #-}
module TypeChecker where

import Data.Map (Map,(!),mapWithKey,assocs,filterWithKey,elems,keys
                ,intersection,intersectionWith,intersectionWithKey
                ,toList,fromList)
import qualified Data.Map as Map
import qualified Data.Traversable as T
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
data TEnv =
  TEnv { index   :: Int   -- for de Bruijn levels
       , env     :: Env
       , verbose :: Bool  -- Should it be verbose and print what it typechecks?
       } deriving (Eq,Show)

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv 0 Empty True
silentEnv  = TEnv 0 Empty False

-- Trace function that depends on the verbosity flag
trace :: String -> Typing ()
trace s = do
  b <- asks verbose
  when b $ liftIO (putStrLn s)

-------------------------------------------------------------------------------
-- | Functions for running computations in the type checker monad

runTyping :: TEnv -> Typing a -> IO (Either String a)
runTyping env t = runErrorT $ runReaderT t env

runDecls :: TEnv -> [Decl] -> IO (Either String TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  return $ addDecls d tenv

runDeclss :: TEnv -> [[Decl]] -> IO (Maybe String,TEnv)
runDeclss tenv []     = return (Nothing, tenv)
runDeclss tenv (d:ds) = do
  x <- runDecls tenv d
  case x of
    Right tenv' -> runDeclss tenv' ds
    Left s      -> return (Just s, tenv)

runInfer :: TEnv -> Ter -> IO (Either String Val)
runInfer lenv e = runTyping lenv (infer e)

-------------------------------------------------------------------------------
-- | Modifiers for the environment

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

-------------------------------------------------------------------------------
-- | Various useful functions

-- Extract the type of a label as a closure
getLblType :: LIdent -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ _ cas) r) = case lookupLabel c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType: " ++ show c)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Monadic version of local
localM :: (TEnv -> Typing TEnv) -> Typing a -> Typing a
localM f r = do
  e <- ask
  a <- f e
  local (const a) r

-- Monadic version of unless
unlessM :: Monad m => m Bool -> m () -> m ()
unlessM mb x = mb >>= flip unless x

-- Constant path: <_> v
constPath :: Val -> Val
constPath = VPath (Name "_")

mkVars :: Int -> Tele -> Env -> [(Ident,Val)]
mkVars k [] _ = []
mkVars k ((x,a):xas) nu =
  let w = mkVar k (eval nu a)
  in (x,w) : mkVars (k+1) xas (Upd nu (x,w))

-- Construct a fuction "(_ : va) -> vb"
mkFun :: Val -> Val -> Val
mkFun va vb = VPi va (eval rho (Lam "_" (Var "a") (Var "b")))
  where rho = Upd (Upd Empty ("a",va)) ("b",vb)

idP = undefined

-- Construct "(x : b) -> IdP (<_> b) (f (g x)) x"
mkSection :: Val -> Val -> Val -> Val
mkSection vb vf vg =
  VPi vb (eval rho (Lam "x" b (idP (Path (Name "_") b) (App f (App g x)) x)))
  where [b,x,f,g] = map Var ["b","x","f","g"]
        rho = Upd (Upd (Upd Empty ("b",vb)) ("f",vf)) ("g",vg)

-- Test if two values are convertible
(===) :: Convertible a => a -> a -> Typing Bool
u === v = conv <$> asks index <*> pure u <*> pure v

-- eval in the typing monad
evalTyping :: Ter -> Typing Val
evalTyping t = eval <$> asks env <*> pure t

-------------------------------------------------------------------------------
-- | The bidirectional type checker

-- Check that t has type a
check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Pi f)       -> checkFam f
  (VU,Sigma f)    -> checkFam f
  (VU,Sum _ _ bs) -> forM_ bs $ \lbl -> case lbl of
    OLabel _ tele -> checkTele tele
    PLabel _ tele t0 t1 -> do
      checkTele tele
      rho <- asks env
      localM (addTele tele) $ do
        check (Ter t rho) t0
        check (Ter t rho) t1
  (VPi va@(Ter (Sum _ _ cas) nu) f,Split _ _ f' ces) -> do
    checkFam f'
    rho <- asks env
    unlessM (f === eval rho f') $ throwError "check: split annotations"
    if map labelName cas == map branchName ces
       then sequence_ [ checkBranch (lbl,nu) f brc (Ter t rho) va
                      | (brc, lbl) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x a' t)  -> do
    check VU a'
    k <- asks index
    rho <- asks env
    unlessM (a === eval rho a') $
      throwError "check: lam types don't match"
    let var = mkVar k a
    local (addTypeVal (x,a)) $ check (app f var) t
  (VSigma a f, Pair t1 t2) -> do
    check a t1
    v <- evalTyping t1
    check (app f v) t2
  (_,Where e d) -> do
    checkDecls d
    local (addDecls d) $ check a e
  (_,Undef _) -> return ()

  (VTPath i a,Path j t) -> do
    let k = fresh (Atom i,Atom j,a)
    local (addSub (j,Atom k)) $ check (a `swap` (i,k)) t
  (VRes a as,u) -> do
    check a u
    rho <- asks env
    -- let vu = eval rho u
    checkSystemWith as (\alpha aalpha -> do
      let ualpha = (eval (rho `face` alpha) u) `face` alpha
      unlessM (ualpha === aalpha) $
        throwError "res")

  -- (VU,IdP a e0 e1) -> do
  --   (a0,a1) <- checkPath (constPath VU) a
  --   check a0 e0
  --   check a1 e1
  -- (VIdP p a0 a1,Path _ e) -> do
  --   (u0,u1) <- checkPath p t
  --   k <- asks index
  --   unless (conv k a0 u0 && conv k a1 u1) $
  --     throwError $ "path endpoints don't match " ++ show e
  (VU,Glue a ts) -> do
    check VU a
    rho <- asks env
    checkGlue (eval rho a) ts
  (VGlue va ts,GlueElem u us) -> do
    check va u
    vu <- evalTyping u
    checkGlueElem vu ts us
  _ -> do
    v <- infer t
    unlessM (v === a) $
      throwError $ "check conv: " ++ show v ++ " /= " ++ show a

-- Check a list of declarations
checkDecls :: [Decl] -> Typing ()
checkDecls d = do
  let (idents, tele, ters) = (declIdents d, declTele d, declTers d)
  trace ("Checking: " ++ unwords idents)
  checkTele tele
  rho <- asks env
  localM (addTele tele) $ checks (tele,rho) ters

-- Check a telescope
checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check VU a
  localM (addType (x,a)) $ checkTele xas

-- Check a family
checkFam :: Ter -> Typing ()
checkFam (Lam x a b) = do
  check VU a
  localM (addType (x,a)) $ check VU b
checkFam x = throwError $ "checkFam: " ++ show x

-- Check that a system is compatible
checkCompSystem :: System Val -> Typing ()
checkCompSystem vus = do
  k <- asks index
  unless (isCompSystem k vus)
    (throwError $ "Incompatible system " ++ show vus)

-- Check the values at corresponding faces with a function, assumes
-- systems have the same faces
checkSystemsWith ::
  System a -> System b -> (Face -> a -> b -> Typing c) -> Typing ()
checkSystemsWith us vs f = sequence_ $ elems $ intersectionWithKey f us vs

-- Check the faces of a system
checkSystemWith :: System a -> (Face -> a -> Typing b) -> Typing ()
checkSystemWith us f = sequence_ $ elems $ mapWithKey f us

-- Check a glueElem
checkGlueElem :: Val -> System Val -> System Ter -> Typing ()
checkGlueElem vu ts us = do
  unless (keys ts == keys us)
    (throwError ("Keys don't match in " ++ show ts ++ " and " ++ show us))
  rho <- asks env
  checkSystemsWith ts us (\_ vt u -> check (hisoDom vt) u)
  let vus = evalSystem rho us
  checkSystemsWith ts vus (\alpha vt vAlpha ->
    unlessM (app (hisoFun vt) vAlpha === (vu `face` alpha)) $
      throwError $ "Image of glueElem component " ++ show vAlpha ++
                   " doesn't match " ++ show vu)
  checkCompSystem vus

checkGlue :: Val -> System Ter -> Typing ()
checkGlue va ts = do
  checkSystemWith ts (\alpha tAlpha -> checkIso (va `face` alpha) tAlpha)
  rho <- asks env
  checkCompSystem (evalSystem rho ts)

-- An iso for a type b is a five-tuple: (a,f,g,r,s)   where
--  a : U
--  f : a -> b
--  g : b -> a
--  s : forall (y : b), f (g y) = y
--  t : forall (x : a), g (f x) = x
checkIso :: Val -> Ter -> Typing ()
checkIso vb (Pair a (Pair f (Pair g (Pair s t)))) = do
  check VU a
  va <- evalTyping a
  check (mkFun va vb) f
  check (mkFun vb va) g
  vf <- evalTyping f
  vg <- evalTyping g
  check (mkSection vb vf vg) s
  check (mkSection va vg vf) t

checkBranch :: (Label,Env) -> Val -> Branch -> Val -> Val -> Typing ()
checkBranch (OLabel _ tele,nu) f (OBranch c ns e) _ _ = do
  k <- asks index
  let us = map snd $ mkVars k tele nu
  local (addBranch (zip ns us) (tele,nu)) $ check (app f (VCon c us)) e
checkBranch (PLabel _ tele t0 t1,nu) f (PBranch c ns i e) g va = do
  k <- asks index
  let us  = mkVars k tele nu
      vus = map snd us
      vt0 = eval (upds nu us) t0
      vt1 = eval (upds nu us) t1
  checkFresh i
  local (addBranch (zip ns vus) (tele,nu)) $ do
    local (addSub (i,Atom i)) $
      check (app f (VPCon c va vus (Atom i))) e
    rho <- asks env
    k'  <- asks index
    unless (conv k' (eval (Sub rho (i,Dir 0)) e) (app g vt0) &&
            conv k' (eval (Sub rho (i,Dir 1)) e) (app g vt1)) $
      throwError "Endpoints of branch don't match"

checkFormula :: Formula -> Typing ()
checkFormula phi = do
  rho <- asks env
  let dom = domainEnv rho
  unless (all (\x -> x `elem` dom) (support phi)) $
    throwError $ "checkFormula: " ++ show phi

checkFresh :: Name -> Typing ()
checkFresh i = do
  rho <- asks env
  when (i `elem` support rho)
    (throwError $ show i ++ " is already declared")

-- Check that a term is a path and output the source and target
checkPath :: Val -> Ter -> Typing (Val,Val)
checkPath v (Path i a) = do
  rho <- asks env
  checkFresh i
  local (addSub (i,Atom i)) $ check (v @@ i) a
  return (eval (Sub rho (i,Dir 0)) a,eval (Sub rho (i,Dir 1)) a)
-- checkPath v t = do
--   vt <- infer t
--   case vt of
--     VIdP a a0 a1 -> do
--       unlessM (a === v) $ throwError "checkPath"
--       return (a0,a1)
--     _ -> throwError $ show vt ++ " is not a path"

-- Return system such that:
--   rhoalpha |- p_alpha : Id (va alpha) (t0 rhoalpha) ualpha
-- Moreover, check that the system ps is compatible.
checkPathSystem :: Ter -> Val -> System Ter -> Typing (System Val)
checkPathSystem t0 va ps = do
  rho <- asks env
  checkCompSystem (evalSystem rho ps)
  T.sequence $ mapWithKey (\alpha pAlpha -> do
    (a0,a1) <- checkPath (constPath (va `face` alpha)) pAlpha
    unlessM (a0 === eval (rho `face` alpha) t0) $
      throwError $ "Incompatible system with " ++ show t0
    return a1) ps

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks _              []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  check (eval nu a) e
  v' <- evalTyping e
  checks (xas,Upd nu (x,v')) es
checks _              _      = throwError "checks"

-- infer the type of e
infer :: Ter -> Typing Val
infer e = case e of
  U     -> return VU  -- U : U
  Var n -> lookType n <$> asks env
  App t u -> do
    c <- infer t
    case c of
      VPi a f -> do
        check a u
        v <- evalTyping u
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
        v <- evalTyping t
        return $ app f (fstVal v)
      _          -> throwError $ show c ++ " is not a sigma-type"
  Where t d -> do
    checkDecls d
    local (addDecls d) $ infer t
  -- AppFormula e phi -> do
  --   checkFormula phi
  --   t <- infer e
  --   case t of
  --     VIdP a _ _ -> return $ a @@ phi
  --     _ -> throwError (show e ++ " is not a path")

  AppFormula e phi -> do
    checkFormula phi
    t <- infer e
    case t of
      VTPath i a -> return $ a `act` (i,phi)
      _ -> throwError (show e ++ " is not a path")

  Trans p t -> do
    (a0,a1) <- checkPath (constPath VU) p
    check a0 t
    return a1

  -- Comp a t0 ps -> do
  --   check VU a
  --   va <- evalTyping a
  --   check va t0
  --   checkPathSystem t0 va ps
  --   return va
  CompElem a es u us -> do
    check VU a
    rho <- asks env
    let va = eval rho a
    ts <- checkPathSystem a VU es
    let ves = evalSystem rho es
    unless (keys es == keys us)
      (throwError ("Keys don't match in " ++ show es ++ " and " ++ show us))
    check va u
    let vu = eval rho u
    checkSystemsWith ts us (\_ -> check)
    let vus = evalSystem rho us
    checkCompSystem vus
    checkSystemsWith ves vus (\alpha eA vuA ->
      unlessM (transNegLine eA vuA === (vu `face` alpha)) $
        throwError $ "Malformed compElem: " ++ show us)
    return $ compLine VU va ves
  ElimComp a es u -> do
    check VU a
    rho <- asks env
    let va = eval rho a
    checkPathSystem a VU es
    let ves = evalSystem rho es
    check (compLine VU va ves) u
    return va
  PCon c a es phi -> do
    check VU a
    va <- evalTyping a
    (bs,nu) <- getLblType c va
    checks (bs,nu) es
    checkFormula phi
    return va
  _ -> throwError ("infer " ++ show e)

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
