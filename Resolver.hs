{-# LANGUAGE TupleSections, ParallelListComp #-}

-- | Convert the concrete syntax into the syntax of cubical TT.
module Resolver where

import Exp.Abs
import qualified TT

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Error (throwError)
import Control.Monad (when)
import Data.Functor.Identity
import Data.List (nub)
import Prelude hiding (pi)

type Ter  = TT.Ter

-- | Useful auxiliary functions

-- Applicative cons
(<:>) :: Applicative f => f a -> f [a] -> f [a]
a <:> b = (:) <$> a <*> b

-- Un-something functions
unAIdent :: AIdent -> String
unAIdent (AIdent (_,x)) = x

unVar :: Exp -> Maybe AIdent
unVar (Var x) = Just x
unVar _       = Nothing

unWhere :: ExpWhere -> Exp
unWhere (Where e ds) = Let ds e
unWhere (NoWhere e)  = e

-- Tail recursive form to transform a sequence of applications
-- App (App (App u v) ...) w  into (u, [v, …, w])
-- (cleaner than the previous version of unApps)
unApps :: Exp -> [Exp] -> (Exp, [Exp])
unApps (App u v) ws = unApps u (v : ws)
unApps u         ws = (u, ws)

-- Turns an expression of the form App (... (App id1 id2) ... idn)
-- into a list of idents
appsToIdents :: Exp -> Maybe [AIdent]
appsToIdents = mapM unVar . uncurry (:) . flip unApps []

-- Flatten a tele
flattenTele :: [Tele] -> [(AIdent,Exp)]
flattenTele tele = [ (i,typ) | Tele id ids typ <- tele, i <- id:ids ]

-- Flatten a PTele
flattenPTele :: [PTele] -> Resolver [(AIdent,Exp)]
flattenPTele []                   = return []
flattenPTele (PTele exp typ : xs) = case appsToIdents exp of
  Just ids -> do 
    pt <- flattenPTele xs
    return $ map (,typ) ids ++ pt
  Nothing -> throwError "malformed ptele"

-------------------------------------------------------------------------------
-- | Resolver and environment

data SymKind = Variable | Constructor
  deriving (Eq,Show)

-- local environment for constructors
data Env = Env { envModule :: String,
                 variables :: [(TT.Binder,SymKind)] }
  deriving (Eq,Show)

type Resolver a = ReaderT Env (ErrorT String Identity) a

emptyEnv :: Env
emptyEnv = Env "" []

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runErrorT $ runReaderT x emptyEnv

updateModule :: String -> Env -> Env
updateModule mod e = e{envModule = mod}

insertBinder :: (TT.Binder,SymKind) -> Env -> Env
insertBinder (x@(n,_),var) e
  | n == "_" || n == "undefined" = e
  | otherwise                    = e{variables = (x,var) : variables e}

insertBinders :: [(TT.Binder,SymKind)] -> Env -> Env
insertBinders = flip $ foldr insertBinder

insertVar :: TT.Binder -> Env -> Env
insertVar x = insertBinder (x,Variable)

insertVars :: [TT.Binder] -> Env -> Env
insertVars = flip $ foldr insertVar

insertCon :: TT.Binder -> Env -> Env
insertCon x = insertBinder (x,Constructor)

insertCons :: [TT.Binder] -> Env -> Env
insertCons = flip $ foldr insertCon

getModule :: Resolver String
getModule = envModule <$> ask

getVariables :: Resolver [(TT.Binder,SymKind)]
getVariables = variables <$> ask

getLoc :: (Int,Int) -> Resolver TT.Loc
getLoc l = TT.Loc <$> getModule <*> pure l

resolveAIdent :: AIdent -> Resolver TT.Binder
resolveAIdent (AIdent (l,x)) = (x,) <$> getLoc l
 
resolveVar :: AIdent -> Resolver Ter
resolveVar (AIdent (l,x))
  | (x == "_") || (x == "undefined") = TT.Undef <$> getLoc l
  | otherwise = do
    modName <- getModule
    vars    <- getVariables
    case TT.lookupIdent x vars of
      Just Variable    -> return $ TT.Var x
      Just Constructor -> return $ TT.Con x []
      _ -> throwError $ "Cannot resolve variable " ++ x ++ " at position " ++
                        show l ++ " in module " ++ modName

lam :: (AIdent,Exp) -> Resolver Ter -> Resolver Ter
lam (a,t) e = do
  x <- resolveAIdent a
  t' <- resolveExp t
  TT.Lam x t' <$> local (insertVar x) e

lams :: [(AIdent,Exp)] -> Resolver Ter -> Resolver Ter
lams = flip $ foldr lam

bind :: (Ter -> Ter) -> (AIdent,Exp) -> Resolver Ter -> Resolver Ter
bind f (x,t) e = f <$> lam (x,t) e

binds :: (Ter -> Ter) -> [(AIdent,Exp)] -> Resolver Ter -> Resolver Ter
binds f = flip $ foldr $ bind f

resolveExp :: Exp -> Resolver Ter
resolveExp U            = return TT.U
resolveExp (Var x)      = resolveVar x
resolveExp (App t s)    = TT.mkApps <$> resolveExp x <*> mapM resolveExp xs
  where (x,xs) = unApps t [s]
resolveExp (Sigma ptele b)  = do
  tele <- flattenPTele ptele
  binds TT.Sigma tele (resolveExp b)
resolveExp (Pi ptele b)     = do
  tele <- flattenPTele ptele
  binds TT.Pi tele (resolveExp b)
resolveExp (Fun a b)    = bind TT.Pi (AIdent ((0,0),"_"), a) (resolveExp b)
resolveExp (Lam ptele t) = do
  tele <- flattenPTele ptele
  lams tele (resolveExp t)
resolveExp (Fst t)      = TT.Fst <$> resolveExp t
resolveExp (Snd t)      = TT.Snd <$> resolveExp t
resolveExp (Pair t0 t1) = TT.SPair <$> resolveExp t0 <*> resolveExp t1
resolveExp (Let decls e) = do
  (rdecls,names) <- resolveDecls decls
  TT.mkWheres rdecls <$> local (insertBinders names) (resolveExp e)

resolveWhere :: ExpWhere -> Resolver Ter
resolveWhere = resolveExp . unWhere

resolveBranch :: Branch -> Resolver (TT.Label,([TT.Binder],Ter))
resolveBranch (Branch lbl args e) = do
    binders <- mapM resolveAIdent args
    re      <- local (insertVars binders) $ resolveWhere e
    return (unAIdent lbl, (binders, re))

resolveTele :: [(AIdent,Exp)] -> Resolver TT.Tele
resolveTele []        = return []
resolveTele ((i,d):t) = do
  x <- resolveAIdent i
  ((x,) <$> resolveExp d) <:> local (insertVar x) (resolveTele t)

resolveLabel :: Label -> Resolver (TT.Binder,TT.Tele)
resolveLabel (Label n vdecl) = (,) <$> resolveAIdent n <*> resolveTele (flattenTele vdecl)

declsLabels :: [Decl] -> Resolver [TT.Binder]
declsLabels decls = mapM resolveAIdent [ lbl | Label lbl _ <- sums ]
  where sums = concat [ sum | DeclData _ _ sum <- decls ]

piToFam :: Exp -> Resolver Ter
piToFam (Fun a b) = lam (AIdent ((0,0),"_"),a) $ resolveExp b
piToFam (Pi ptele b) = do
  (x,a):tele <- flattenPTele ptele
  lam (x,a) (binds TT.Pi tele (resolveExp b))

-- Resolve Data or Def or Split declaration
resolveDecl :: Decl -> Resolver ((TT.Binder,(Ter,Ter)),[(TT.Binder,SymKind)])
resolveDecl (DeclDef n tele t body) = do
  f <- resolveAIdent n
  let tele' = flattenTele tele
  d <- lams tele' (resolveWhere body)
  a <- binds TT.Pi tele' (resolveExp t)
  return ((f,(a,d)),[(f,Variable)])
resolveDecl (DeclData n tele sums) = do
  f <- resolveAIdent n
  let tele' = flattenTele tele
  d <- lams tele' $ local (insertVar f) $
       TT.Sum <$> resolveAIdent n <*> mapM resolveLabel sums
  a <- binds TT.Pi tele' (return TT.U)
  cs <- mapM resolveAIdent [ lbl | Label lbl _ <- sums ]
  return ((f,(a,d)),(f,Variable):map (,Constructor) cs)
resolveDecl (DeclSplit n tele t brs) = do
  f <- resolveAIdent n
  let tele' = flattenTele tele
  vars <- mapM resolveAIdent $ map fst tele'
  fam <- local (insertVars vars) $ piToFam t
  brs' <- local (insertVars (f:vars)) (mapM resolveBranch brs)
  a <- binds TT.Pi tele' (resolveExp t)
  loc  <- getLoc (case brs of Branch (AIdent (l,_)) _ _:_ -> l ; _ -> (0,0))
  body <- lams tele' (return $ TT.Split loc fam brs')
  return $ ((f,(a,body)),[(f,Variable)])

-- Resolve mutual declarations (possibly one)
-- resolveMutuals :: [Decl] -> Resolver (TT.Decls,[(TT.Binder,SymKind)])
-- resolveMutuals decls = do
--     binders <- mapM resolveAIdent idents
--     cs      <- declsLabels decls
--     let cns = map fst cs ++ names
--     when (nub cns /= cns) $
--       throwError $ "Duplicated constructor or ident: " ++ show cns
--     rddecls <-
--       mapM (local (insertVars binders . insertCons cs) . resolveDDecl) ddecls
--     when (names /= map fst rddecls) $
--       throwError $ "Mismatching names in " ++ show decls
--     rtdecls <- resolveTele tdecls
--     return ([ (x,t,d) | (x,t) <- rtdecls | (_,d) <- rddecls ],
--             map (,Constructor) cs ++ map (,Variable) binders)
--   where
--     idents = [ x | DeclType x _ <- decls ]
--     names  = [ unAIdent x | x <- idents ]
--     tdecls = [ (x,t) | DeclType x t <- decls ]
--     ddecls = [ t | t <- decls, not $ isTDecl t ]
--     isTDecl d = case d of DeclType{} -> True; _ -> False

-- Resolve declarations
resolveDecls :: [Decl] -> Resolver ([TT.Decls],[(TT.Binder,SymKind)])
resolveDecls []                   = return ([],[])
resolveDecls (d:ds) = do
    (rtd,names)  <- resolveDecl d     --  (TT.Binder,(Ter,Ter))
    (rds,names') <- local (insertBinders names) $ resolveDecls ds
    return ([rtd] : rds, names' ++ names)
-- resolveDecls (DeclMutual defs : ds) = do
--   (rdefs,names)  <- resolveMutuals defs
--   (rds,  names') <- local (insertBinders names) $ resolveDecls ds
--   return (rdefs : rds, names' ++ names)
-- resolveDecls (decl:_) = throwError $ "Invalid declaration: " ++ show decl

resolveModule :: Module -> Resolver ([TT.Decls],[(TT.Binder,SymKind)])
resolveModule (Module n imports decls) =
  local (updateModule $ unAIdent n) $ resolveDecls decls

resolveModules :: [Module] -> Resolver ([TT.Decls],[(TT.Binder,SymKind)])
resolveModules []         = return ([],[])
resolveModules (mod:mods) = do
  (rmod, names)  <- resolveModule mod
  (rmods,names') <- local (insertBinders names) $ resolveModules mods
  return (rmod ++ rmods, names' ++ names)
