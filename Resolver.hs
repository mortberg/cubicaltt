{-# LANGUAGE TupleSections, ParallelListComp #-}

-- | Convert the concrete syntax into the syntax of cubical TT.
module Resolver where

import Exp.Abs
import qualified CTT

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Error hiding (throwError)
import Control.Monad.Error (throwError)
import Control.Monad (when)
import Data.Functor.Identity
import Data.List (nub)
import Prelude hiding (pi)

type Ter = CTT.Ter

-- | Useful auxiliary functions

-- Applicative cons
(<:>) :: Applicative f => f a -> f [a] -> f [a]
a <:> b = (:) <$> a <*> b

-- Un-something functions
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
                 variables :: [(CTT.Binder,SymKind)] }
  deriving (Eq,Show)

type Resolver a = ReaderT Env (ErrorT String Identity) a

emptyEnv :: Env
emptyEnv = Env "" []

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runErrorT $ runReaderT x emptyEnv

updateModule :: String -> Env -> Env
updateModule mod e = e{envModule = mod}

insertBinder :: (CTT.Binder,SymKind) -> Env -> Env
insertBinder (x@(n,_),var) e
  | n == "_" || n == "undefined" = e
  | otherwise                    = e{variables = (x,var) : variables e}

insertBinders :: [(CTT.Binder,SymKind)] -> Env -> Env
insertBinders = flip $ foldr insertBinder

insertVar :: CTT.Binder -> Env -> Env
insertVar x = insertBinder (x,Variable)

insertVars :: [CTT.Binder] -> Env -> Env
insertVars = flip $ foldr insertVar

getLoc :: (Int,Int) -> Resolver CTT.Loc
getLoc l = CTT.Loc <$> asks envModule <*> pure l

noLoc :: AIdent
noLoc = AIdent ((0,0),"_")
           
resolveAIdent :: AIdent -> Resolver CTT.Binder
resolveAIdent (AIdent (l,x)) = (x,) <$> getLoc l
 
resolveVar :: AIdent -> Resolver Ter
resolveVar (AIdent (l,x))
  | (x == "_") || (x == "undefined") = CTT.Undef <$> getLoc l
  | otherwise = do
    modName <- asks envModule
    vars    <- asks variables
    case CTT.lookupIdent x vars of
      Just Variable    -> return $ CTT.Var x
      Just Constructor -> return $ CTT.Con x []
      _ -> throwError $ "Cannot resolve variable " ++ x ++ " at position " ++
                        show l ++ " in module " ++ modName

lam :: (AIdent,Exp) -> Resolver Ter -> Resolver Ter
lam (a,t) e = do
  x  <- resolveAIdent a
  t' <- resolveExp t
  CTT.Lam x t' <$> local (insertVar x) e

lams :: [(AIdent,Exp)] -> Resolver Ter -> Resolver Ter
lams = flip $ foldr lam

bind :: (Ter -> Ter) -> (AIdent,Exp) -> Resolver Ter -> Resolver Ter
bind f (x,t) e = f <$> lam (x,t) e

binds :: (Ter -> Ter) -> [(AIdent,Exp)] -> Resolver Ter -> Resolver Ter
binds f = flip $ foldr $ bind f

resolveExp :: Exp -> Resolver Ter
resolveExp e = case e of
  U             -> return CTT.U
  Var x         -> resolveVar x
  App t s       -> CTT.mkApps <$> resolveExp x <*> mapM resolveExp xs
      where (x,xs) = unApps t [s]
  Sigma ptele b -> do
    tele <- flattenPTele ptele
    binds CTT.Sigma tele (resolveExp b)
  Pi ptele b    -> do
    tele <- flattenPTele ptele
    binds CTT.Pi tele (resolveExp b)
  Fun a b       -> bind CTT.Pi (noLoc,a) (resolveExp b)
  Lam ptele t   -> do
    tele <- flattenPTele ptele
    lams tele (resolveExp t)
  Fst t         -> CTT.Fst <$> resolveExp t
  Snd t         -> CTT.Snd <$> resolveExp t
  Pair t0 t1    -> CTT.SPair <$> resolveExp t0 <*> resolveExp t1
  Let decls e   -> do
    (rdecls,names) <- resolveDecls decls
    CTT.mkWheres rdecls <$> local (insertBinders names) (resolveExp e)

resolveWhere :: ExpWhere -> Resolver Ter
resolveWhere = resolveExp . unWhere

resolveBranch :: Branch -> Resolver (CTT.Label,([CTT.Binder],Ter))
resolveBranch (Branch (AIdent (_,lbl)) args e) = do
    binders <- mapM resolveAIdent args
    re      <- local (insertVars binders) $ resolveWhere e
    return (lbl, (binders, re))

resolveTele :: [(AIdent,Exp)] -> Resolver CTT.Tele
resolveTele []        = return []
resolveTele ((i,d):t) = do
  x <- resolveAIdent i
  ((x,) <$> resolveExp d) <:> local (insertVar x) (resolveTele t)

resolveLabel :: Label -> Resolver (CTT.Binder,CTT.Tele)
resolveLabel (Label n vdecl) = (,) <$> resolveAIdent n <*> resolveTele (flattenTele vdecl)

declsLabels :: [Decl] -> Resolver [CTT.Binder]
declsLabels decls = mapM resolveAIdent [ lbl | Label lbl _ <- sums ]
  where sums = concat [ sum | DeclData _ _ sum <- decls ]

piToFam :: Exp -> Resolver Ter
piToFam (Fun a b)    = lam (noLoc,a) $ resolveExp b
piToFam (Pi ptele b) = do
  (x,a):tele <- flattenPTele ptele
  lam (x,a) (binds CTT.Pi tele (resolveExp b))

-- Resolve Data or Def or Split declarations
resolveDecl :: Decl -> Resolver (CTT.Decl,[(CTT.Binder,SymKind)])
resolveDecl d = case d of
  DeclDef n tele t body -> do
    f <- resolveAIdent n
    let tele' = flattenTele tele
    a <- binds CTT.Pi tele' (resolveExp t)
    d <- lams tele' (resolveWhere body)
    return ((f,(a,d)),[(f,Variable)])
  DeclData n tele sums -> do
    f <- resolveAIdent n
    let tele' = flattenTele tele
    a  <- binds CTT.Pi tele' (return CTT.U)
    d  <- lams tele' $ local (insertVar f) $
            CTT.Sum <$> resolveAIdent n <*> mapM resolveLabel sums
    cs <- mapM resolveAIdent [ lbl | Label lbl _ <- sums ]
    return ((f,(a,d)),(f,Variable):map (,Constructor) cs)
  DeclSplit n tele t brs -> do
    f <- resolveAIdent n
    let tele' = flattenTele tele
        loc   = snd f
    a    <- binds CTT.Pi tele' (resolveExp t)
    vars <- mapM resolveAIdent $ map fst tele'
    fam  <- local (insertVars vars) $ piToFam t
    brs' <- local (insertVars (f:vars)) (mapM resolveBranch brs)
    body <- lams tele' (return $ CTT.Split loc fam brs')
    return ((f,(a,body)),[(f,Variable)])

resolveDecls :: [Decl] -> Resolver ([CTT.Decls],[(CTT.Binder,SymKind)])
resolveDecls []     = return ([],[])
resolveDecls (d:ds) = do
    (rtd,names)  <- resolveDecl d
    (rds,names') <- local (insertBinders names) $ resolveDecls ds
    return ([rtd] : rds, names' ++ names)

resolveModule :: Module -> Resolver ([CTT.Decls],[(CTT.Binder,SymKind)])
resolveModule (Module (AIdent (_,n)) _ decls) =
  local (updateModule n) $ resolveDecls decls

resolveModules :: [Module] -> Resolver ([CTT.Decls],[(CTT.Binder,SymKind)])
resolveModules []         = return ([],[])
resolveModules (mod:mods) = do
  (rmod, names)  <- resolveModule mod
  (rmods,names') <- local (insertBinders names) $ resolveModules mods
  return (rmod ++ rmods, names' ++ names)
