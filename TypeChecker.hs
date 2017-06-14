{-# LANGUAGE TupleSections #-}
module TypeChecker where

import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Data.Map (Map,(!),mapWithKey,assocs,filterWithKey,elems,keys
                ,intersection,intersectionWith,intersectionWithKey
                ,toList,fromList)
import qualified Data.Map as Map
import qualified Data.Traversable as T

import Connections
import CTT
import Eval

-- Type checking monad
type Typing a = ReaderT TEnv (ExceptT String IO) a

-- Environment for type checker
data TEnv =
  TEnv { names   :: [String] -- generated names
       , indent  :: Int
       , env     :: Env
       , verbose :: Bool  -- Should it be verbose and print what it typechecks?
       } deriving (Eq)

verboseEnv, silentEnv :: TEnv
verboseEnv = TEnv [] 0 emptyEnv True
silentEnv  = TEnv [] 0 emptyEnv False

-- Trace function that depends on the verbosity flag
trace :: String -> Typing ()
trace s = do
  b <- asks verbose
  when b $ liftIO (putStrLn s)

-------------------------------------------------------------------------------
-- | Functions for running computations in the type checker monad

runTyping :: TEnv -> Typing a -> IO (Either String a)
runTyping env t = runExceptT $ runReaderT t env

runDecls :: TEnv -> Decls -> IO (Either String TEnv)
runDecls tenv d = runTyping tenv $ do
  checkDecls d
  return $ addDecls d tenv

runDeclss :: TEnv -> [Decls] -> IO (Maybe String,TEnv)
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
addTypeVal (x,a) (TEnv ns ind rho v) =
  let w@(VVar n _) = mkVarNice ns x a
  in TEnv (n:ns) ind (upd (x,w) rho) v

addSub :: (Name,Formula) -> TEnv -> TEnv
addSub iphi (TEnv ns ind rho v) = TEnv ns ind (sub iphi rho) v

addSubs :: [(Name,Formula)] -> TEnv -> TEnv
addSubs = flip $ foldr addSub

addType :: (Ident,Ter) -> TEnv -> TEnv
addType (x,a) tenv@(TEnv _ _ rho _) = addTypeVal (x,eval rho a) tenv

addBranch :: [(Ident,Val)] -> Env -> TEnv -> TEnv
addBranch nvs env (TEnv ns ind rho v) =
  TEnv ([n | (_,VVar n _) <- nvs] ++ ns) ind (upds nvs rho) v

addDecls :: Decls -> TEnv -> TEnv
addDecls d (TEnv ns ind rho v) = TEnv ns ind (def d rho) v

addTele :: Tele -> TEnv -> TEnv
addTele xas lenv = foldl (flip addType) lenv xas

faceEnv :: Face -> TEnv -> TEnv
faceEnv alpha tenv = tenv{env=env tenv `face` alpha}

-------------------------------------------------------------------------------
-- | Various useful functions

-- Extract the type of a label as a closure
getLblType :: LIdent -> Val -> Typing (Tele, Env)
getLblType c (Ter (Sum _ _ cas) r) = case lookupLabel c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType: " ++ show c ++ " in " ++ show cas)
getLblType c (Ter (HSum _ _ cas) r) = case lookupLabel c cas of
  Just as -> return (as,r)
  Nothing -> throwError ("getLblType: " ++ show c ++ " in " ++ show cas)
getLblType c u = throwError ("expected a data type for the constructor "
                             ++ c ++ " but got " ++ show u)

-- Monadic version of unless
unlessM :: Monad m => m Bool -> m () -> m ()
unlessM mb x = mb >>= flip unless x

mkVars :: [String] -> Tele -> Env -> [(Ident,Val)]
mkVars _ [] _           = []
mkVars ns ((x,a):xas) nu =
  let w@(VVar n _) = mkVarNice ns x (eval nu a)
  in (x,w) : mkVars (n:ns) xas (upd (x,w) nu)

-- Test if two values are convertible
(===) :: Convertible a => a -> a -> Typing Bool
u === v = conv <$> asks names <*> pure u <*> pure v

-- eval in the typing monad
evalTyping :: Ter -> Typing Val
evalTyping t = eval <$> asks env <*> pure t

-------------------------------------------------------------------------------
-- | The bidirectional type checker

-- Check that t has type a
check :: Val -> Ter -> Typing ()
check a t = case (a,t) of
  (_,Undef{}) -> return ()
  (_,Hole l)  -> do
      rho <- asks env
      let e = unlines (reverse (contextOfEnv rho))
      ns <- asks names
      trace $ "\nHole at " ++ show l ++ ":\n\n" ++
              e ++ replicate 80 '-' ++ "\n" ++ show (normal ns a)  ++ "\n"
  (_,Con c es) -> do
    (bs,nu) <- getLblType c a
    checks (bs,nu) es
  (VU,Pi f)       -> checkFam f
  (VU,Sigma f)    -> checkFam f
  (VU,Sum _ _ bs) -> forM_ bs $ \lbl -> case lbl of
    OLabel _ tele -> checkTele tele
    PLabel _ tele is ts ->
      throwError $ "check: no path constructor allowed in " ++ show t
  (VU,HSum _ _ bs) -> forM_ bs $ \lbl -> case lbl of
    OLabel _ tele -> checkTele tele
    PLabel _ tele is ts -> do
      checkTele tele
      rho <- asks env
      unless (all (`elem` is) (domain ts)) $
        throwError "names in path label system" -- TODO
      mapM_ checkFresh is
      let iis = zip is (map Atom is)
      local (addSubs iis . addTele tele) $ do
        checkSystemWith ts $ \alpha talpha ->
          local (faceEnv alpha) $
            -- NB: the type doesn't depend on is
            check (Ter t rho) talpha
        rho' <- asks env
        checkCompSystem (evalSystem rho' ts)
  (VPi va@(Ter (Sum _ _ cas) nu) f,Split _ _ ty ces) -> do
    check VU ty
    rho <- asks env
    unlessM (a === eval rho ty) $ throwError "check: split annotations"
    if map labelName cas == map branchName ces
       then sequence_ [ checkBranch (lbl,nu) f brc (Ter t rho) va
                      | (brc, lbl) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (VPi va@(Ter (HSum _ _ cas) nu) f,Split _ _ ty ces) -> do
    check VU ty
    rho <- asks env
    unlessM (a === eval rho ty) $ throwError "check: split annotations"
    if map labelName cas == map branchName ces
       then sequence_ [ checkBranch (lbl,nu) f brc (Ter t rho) va
                      | (brc, lbl) <- zip ces cas ]
       else throwError "case branches does not match the data type"
  (VPi a f,Lam x a' t)  -> do
    check VU a'
    ns <- asks names
    rho <- asks env
    unlessM (a === eval rho a') $
      throwError $ "check: lam types don't match"
        ++ "\nlambda type annotation: " ++ show a'
        ++ "\ndomain of Pi: " ++ show a
        ++ "\nnormal form of type: " ++ show (normal ns a)
    let var = mkVarNice ns x a

    local (addTypeVal (x,a)) $ check (app f var) t
  (VSigma a f, Pair t1 t2) -> do
    check a t1
    v <- evalTyping t1
    check (app f v) t2
  (_,Where e d) -> do
    local (\tenv@TEnv{indent=i} -> tenv{indent=i + 2}) $ checkDecls d
    local (addDecls d) $ check a e
  (VU,PathP a e0 e1) -> do
    (a0,a1) <- checkPLam (constPath VU) a
    check a0 e0
    check a1 e1
  (VPathP p a0 a1,PLam _ e) -> do
    (u0,u1) <- checkPLam p t
    ns <- asks names
    unless (conv ns a0 u0 && conv ns a1 u1) $
      throwError $ "path endpoints don't match for " ++ show e ++ ", got " ++
                   show (u0,u1) ++ ", but expected " ++ show (a0,a1)
  (VU,Glue a ts) -> do
    check VU a
    rho <- asks env
    checkGlue (eval rho a) ts
  (VGlue va ts,GlueElem u us) -> do
    check va u
    vu <- evalTyping u
    checkGlueElem vu ts us
  (VCompU va ves,GlueElem u us) -> do
    check va u
    vu <- evalTyping u
    checkGlueElemU vu ves us
  (VU,Id a a0 a1) -> do
    check VU a
    va <- evalTyping a
    check va a0
    check va a1
  (VId va va0 va1,IdPair w ts) -> do
    check (VPathP (constPath va) va0 va1) w
    vw <- evalTyping w
    checkSystemWith ts $ \alpha tAlpha ->
      local (faceEnv alpha) $ do
        check (va `face` alpha) tAlpha
        vtAlpha <- evalTyping tAlpha
        unlessM (vw `face` alpha === constPath vtAlpha) $
          throwError "malformed eqC"
    rho <- asks env
    checkCompSystem (evalSystem rho ts) -- Not needed
  _ -> do
    v <- infer t
    unlessM (v === a) $
      throwError $ "check conv:\n" ++ show v ++ "\n/=\n" ++ show a

-- Check a list of declarations
checkDecls :: Decls -> Typing ()
checkDecls (MutualDecls _ []) = return ()
checkDecls (MutualDecls l d)  = do
  a <- asks env
  let (idents,tele,ters) = (declIdents d,declTele d,declTers d)
  ind <- asks indent
  trace (replicate ind ' ' ++ "Checking: " ++ unwords idents)
  checkTele tele
  local (addDecls (MutualDecls l d)) $ do
    rho <- asks env
    checks (tele,rho) ters
checkDecls (OpaqueDecl _)      = return ()
checkDecls (TransparentDecl _) = return ()
checkDecls TransparentAllDecl  = return ()

-- Check a telescope
checkTele :: Tele -> Typing ()
checkTele []          = return ()
checkTele ((x,a):xas) = do
  check VU a
  local (addType (x,a)) $ checkTele xas

-- Check a family
checkFam :: Ter -> Typing ()
checkFam (Lam x a b) = do
  check VU a
  local (addType (x,a)) $ check VU b
checkFam x = throwError $ "checkFam: " ++ show x

-- Check that a system is compatible
checkCompSystem :: System Val -> Typing ()
checkCompSystem vus = do
  ns <- asks names
  unless (isCompSystem ns vus)
    (throwError $ "Incompatible system " ++ showSystem vus)

-- Check the values at corresponding faces with a function, assumes
-- systems have the same faces
checkSystemsWith :: System a -> System b -> (Face -> a -> b -> Typing c) ->
                    Typing ()
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
  checkSystemsWith ts us
    (\alpha vt u -> local (faceEnv alpha) $ check (equivDom vt) u)
  let vus = evalSystem rho us
  checkSystemsWith ts vus (\alpha vt vAlpha ->
    unlessM (app (equivFun vt) vAlpha === (vu `face` alpha)) $
      throwError $ "Image of glue component " ++ show vAlpha ++
                   " doesn't match " ++ show vu)
  checkCompSystem vus

-- Check a glueElem against VComp _ ves
checkGlueElemU :: Val -> System Val -> System Ter -> Typing ()
checkGlueElemU vu ves us = do
  unless (keys ves == keys us)
    (throwError ("Keys don't match in " ++ show ves ++ " and " ++ show us))
  rho <- asks env
  checkSystemsWith ves us
    (\alpha ve u -> local (faceEnv alpha) $ check (ve @@ One) u)
  let vus = evalSystem rho us
  checkSystemsWith ves vus (\alpha ve vAlpha ->
    unlessM (eqFun ve vAlpha === (vu `face` alpha)) $
      throwError $ "Transport of glueElem (for compU) component " ++ show vAlpha ++
                   " doesn't match " ++ show vu)
  checkCompSystem vus

checkGlue :: Val -> System Ter -> Typing ()
checkGlue va ts = do
  checkSystemWith ts (\alpha tAlpha -> checkEquiv (va `face` alpha) tAlpha)
  rho <- asks env
  checkCompSystem (evalSystem rho ts)

-- An iso for a type b is a five-tuple: (a,f,g,s,t)   where
--  a : U
--  f : a -> b
--  g : b -> a
--  s : forall (y : b), f (g y) = y
--  t : forall (x : a), g (f x) = x
mkIso :: Val -> Val
mkIso vb = eval rho $
  Sigma $ Lam "a" U $
  Sigma $ Lam "f" (Pi (Lam "_" a b)) $
  Sigma $ Lam "g" (Pi (Lam "_" b a)) $
  Sigma $ Lam "s" (Pi (Lam "y" b $ PathP (PLam (Name "_") b) (App f (App g y)) y)) $
    Pi (Lam "x" a $ PathP (PLam (Name "_") a) (App g (App f x)) x)
  where [a,b,f,g,x,y] = map Var ["a","b","f","g","x","y"]
        rho = upd ("b",vb) emptyEnv

-- An equivalence for a type a is a triple (t,f,p) where
-- t : U
-- f : t -> a
-- p : (x : a) -> isContr ((y:t) * Id a x (f y))
-- with isContr c = (z : c) * ((z' : C) -> Id c z z')
mkEquiv :: Val -> Val
mkEquiv va = eval rho $
  Sigma $ Lam "t" U $
  Sigma $ Lam "f" (Pi (Lam "_" t a)) $
  Pi (Lam "x" a $ iscontrfib)
  where [a,b,f,x,y,s,t,z] = map Var ["a","b","f","x","y","s","t","z"]
        rho = upd ("a",va) emptyEnv
        fib = Sigma $ Lam "y" t (PathP (PLam (Name "_") a) x (App f y))
        iscontrfib = Sigma $ Lam "s" fib $
                     Pi $ Lam "z" fib $ PathP (PLam (Name "_") fib) s z

checkEquiv :: Val -> Ter -> Typing ()
checkEquiv va equiv = check (mkEquiv va) equiv

checkIso :: Val -> Ter -> Typing ()
checkIso vb iso = check (mkIso vb) iso

checkBranch :: (Label,Env) -> Val -> Branch -> Val -> Val -> Typing ()
checkBranch (OLabel _ tele,nu) f (OBranch c ns e) _ _ = do
  ns' <- asks names
  let us = map snd $ mkVars ns' tele nu
  local (addBranch (zip ns us) nu) $ check (app f (VCon c us)) e
checkBranch (PLabel _ tele is ts,nu) f (PBranch c ns js e) g va = do
  ns' <- asks names
  -- mapM_ checkFresh js
  let us   = mkVars ns' tele nu
      vus  = map snd us
      js'  = map Atom js
      vts  = evalSystem (subs (zip is js') (upds us nu)) ts
      vgts = intersectionWith app (border g vts) vts
  local (addSubs (zip js js') . addBranch (zip ns vus) nu) $ do
    check (app f (VPCon c va vus js')) e
    ve  <- evalTyping e -- TODO: combine with next two lines?
    let veborder = border ve vts
    unlessM (veborder === vgts) $
      throwError $ "Faces in branch for " ++ show c ++ " don't match:"
                   ++ "\ngot\n" ++ showSystem veborder ++ "\nbut expected\n"
                   ++ showSystem vgts

checkFormula :: Formula -> Typing ()
checkFormula phi = do
  rho <- asks env
  let dom = domainEnv rho
  unless (all (`elem` dom) (support phi)) $
    throwError $ "checkFormula: " ++ show phi

checkFresh :: Name -> Typing ()
checkFresh i = do
  rho <- asks env
  when (i `elem` support rho)
    (throwError $ show i ++ " is already declared")

-- Check that a term is a PLam and output the source and target
checkPLam :: Val -> Ter -> Typing (Val,Val)
checkPLam v (PLam i a) = do
  rho <- asks env
  -- checkFresh i
  local (addSub (i,Atom i)) $ check (v @@ i) a
  return (eval (sub (i,Dir 0) rho) a,eval (sub (i,Dir 1) rho) a)
checkPLam v t = do
  vt <- infer t
  case vt of
    VPathP a a0 a1 -> do
      unlessM (a === v) $ throwError (
        "checkPLam\n" ++ show v ++ "\n/=\n" ++ show a)
      return (a0,a1)
    _ -> throwError $ show vt ++ " is not a path"

-- Return system such that:
--   rhoalpha |- p_alpha : Id (va alpha) (t0 rhoalpha) ualpha
-- Moreover, check that the system ps is compatible.
checkPLamSystem :: Ter -> Val -> System Ter -> Typing (System Val)
checkPLamSystem t0 va ps = do
  rho <- asks env
  v <- T.sequence $ mapWithKey (\alpha pAlpha ->
    local (faceEnv alpha) $ do
      rhoAlpha <- asks env
      (a0,a1)  <- checkPLam (va `face` alpha) pAlpha
      unlessM (a0 === eval rhoAlpha t0) $
        throwError $ "Incompatible system " ++ showSystem ps ++
                     ", component\n " ++ show pAlpha ++
                     "\nincompatible with\n " ++ show t0 ++
                     "\na0 = " ++ show a0 ++
                     "\nt0alpha = " ++ show (eval rhoAlpha t0) ++
                     "\nva = " ++ show va
      return a1) ps
  checkCompSystem (evalSystem rho ps)
  return v

checks :: (Tele,Env) -> [Ter] -> Typing ()
checks ([],_)         []     = return ()
checks ((x,a):xas,nu) (e:es) = do
  check (eval nu a) e
  v' <- evalTyping e
  checks (xas,upd (x,v') nu) es
checks _              _      =
  throwError "checks: incorrect number of arguments"

-- infer the type of e
infer :: Ter -> Typing Val
infer e = case e of
  U           -> return VU  -- U : U
  Var n       -> lookType n <$> asks env
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
  UnGlueElem e _ -> do
    t <- infer e
    case t of
     VGlue a _ -> return a
     _ -> throwError (show t ++ " is not a Glue")
  AppFormula e phi -> do
    checkFormula phi
    t <- infer e
    case t of
      VPathP a _ _ -> return $ a @@ phi
      _ -> throwError (show e ++ " is not a path")
  Comp a t0 ps -> do
    (va0, va1) <- checkPLam (constPath VU) a
    va <- evalTyping a
    check va0 t0
    checkPLamSystem t0 va ps
    return va1
  Fill a t0 ps -> do
    (va0, va1) <- checkPLam (constPath VU) a
    va <- evalTyping a
    check va0 t0
    checkPLamSystem t0 va ps
    vt  <- evalTyping t0
    rho <- asks env
    let vps = evalSystem rho ps
    return (VPathP va vt (compLine va vt vps))
  PCon c a es phis -> do
    check VU a
    va <- evalTyping a
    (bs,nu) <- getLblType c va
    checks (bs,nu) es
    mapM_ checkFormula phis
    return va
  IdJ a u c d x p -> do
    check VU a
    va <- evalTyping a
    check va u
    vu <- evalTyping u
    let refu = VIdPair (constPath vu) $ mkSystem [(eps,vu)]
    rho <- asks env
    let z = Var "z"
        ctype = eval rho $ Pi $ Lam "z" a $ Pi $ Lam "_" (Id a u z) U
    check ctype c
    vc <- evalTyping c
    check (app (app vc vu) refu) d
    check va x
    vx <- evalTyping x
    check (VId va vu vx) p
    vp <- evalTyping p
    return (app (app vc vx) vp)
  IdComp a u v w p q -> do
    check VU a
    va <- evalTyping a
    check va u
    vu <- evalTyping u
    check va v
    vv <- evalTyping v
    check va w
    vw <- evalTyping w
    let vIduv = VId va vu vv
    let vIdvw = VId va vv vw
    check vIduv p
    check vIdvw q
    return (VId va vu vw)
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
