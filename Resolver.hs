{-# LANGUAGE TupleSections #-}

-- | Convert the concrete syntax into the syntax of cubical TT.
module Resolver where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity
import Data.List (nub)
import Data.Map (Map,(!))
import qualified Data.Map as Map

import Exp.Abs
import CTT (Ter,Ident,Loc(..),mkApps,mkWheres)
import qualified CTT
import Connections (negFormula,andFormula,orFormula)
import qualified Connections as C

-- | Useful auxiliary functions

-- Applicative cons
(<:>) :: Applicative f => f a -> f [a] -> f [a]
a <:> b = (:) <$> a <*> b

-- Un-something functions
unVar :: Exp -> Maybe Ident
unVar (Var (AIdent (_,x))) = Just x
unVar _                    = Nothing

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
appsToIdents :: Exp -> Maybe [Ident]
appsToIdents = mapM unVar . uncurry (:) . flip unApps []

-- Flatten a tele
flattenTele :: [Tele] -> [(Ident,Exp)]
flattenTele tele =
  [ (unAIdent i,typ) | Tele id ids typ <- tele, i <- id:ids ]

-- Flatten a PTele
flattenPTele :: [PTele] -> Resolver [(Ident,Exp)]
flattenPTele []                   = return []
flattenPTele (PTele exp typ : xs) = case appsToIdents exp of
  Just ids -> do
    pt <- flattenPTele xs
    return $ map (,typ) ids ++ pt
  Nothing -> throwError "malformed ptele"

-------------------------------------------------------------------------------
-- | Resolver and environment

data SymKind = Variable | Constructor | PConstructor | Name
  deriving (Eq,Show)

-- local environment for constructors
data Env = Env { envModule :: String,
                 variables :: [(Ident,SymKind)] }
  deriving (Eq,Show)

type Resolver a = ReaderT Env (ExceptT String Identity) a

emptyEnv :: Env
emptyEnv = Env "" []

runResolver :: Resolver a -> Either String a
runResolver x = runIdentity $ runExceptT $ runReaderT x emptyEnv

updateModule :: String -> Env -> Env
updateModule mod e = e{envModule = mod}

insertIdent :: (Ident,SymKind) -> Env -> Env
insertIdent (n,var) e
  | n == "_"  = e
  | otherwise = e{variables = (n,var) : variables e}

insertIdents :: [(Ident,SymKind)] -> Env -> Env
insertIdents = flip $ foldr insertIdent

insertName :: AIdent -> Env -> Env
insertName (AIdent (_,x)) = insertIdent (x,Name)

insertVar :: Ident -> Env -> Env
insertVar x = insertIdent (x,Variable)

insertVars :: [Ident] -> Env -> Env
insertVars = flip $ foldr insertVar

insertAIdent :: AIdent -> Env -> Env
insertAIdent (AIdent (_,x)) = insertIdent (x,Variable)

insertAIdents :: [AIdent] -> Env -> Env
insertAIdents  = flip $ foldr insertAIdent

getLoc :: (Int,Int) -> Resolver Loc
getLoc l = Loc <$> asks envModule <*> pure l

unAIdent :: AIdent -> Ident
unAIdent (AIdent (_,x)) = x

resolveName :: AIdent -> Resolver C.Name
resolveName (AIdent (l,x)) = do
  modName <- asks envModule
  vars <- asks variables
  case lookup x vars of
    Just Name -> return $ C.Name x
    _ -> throwError $ "Cannot resolve name " ++ x ++ " at position " ++
                      show l ++ " in module " ++ modName

resolveVar :: AIdent -> Resolver Ter
resolveVar (AIdent (l,x)) = do
  modName <- asks envModule
  vars    <- asks variables
  case lookup x vars of
    Just Variable    -> return $ CTT.Var x
    Just Constructor -> return $ CTT.Con x []
    Just PConstructor -> throwError $ "The path constructor " ++ x ++ " is used as a"
                                   ++ " variable at " ++ show l ++ " in " ++ modName
                                   ++ " (path constructors should have their type in"
                                   ++ " curly braces as first argument)"
    Just Name        ->
     throwError $ "Name " ++ x ++ " used as a variable at position " ++
                   show l ++ " in module " ++ modName
    _ -> throwError $ "Cannot resolve variable " ++ x ++ " at position " ++
                      show l ++ " in module " ++ modName

lam :: (Ident,Exp) -> Resolver Ter -> Resolver Ter
lam (a,t) e = CTT.Lam a <$> resolveExp t <*> local (insertVar a) e

lams :: [(Ident,Exp)] -> Resolver Ter -> Resolver Ter
lams = flip $ foldr lam

path :: AIdent -> Resolver Ter -> Resolver Ter
path i e = CTT.Path (C.Name (unAIdent i)) <$> local (insertName i) e

paths :: [AIdent] -> Resolver Ter -> Resolver Ter
paths [] _ = throwError "Empty path lambda"
paths xs e = foldr path e xs

bind :: (Ter -> Ter) -> (Ident,Exp) -> Resolver Ter -> Resolver Ter
bind f (x,t) e = f <$> lam (x,t) e

binds :: (Ter -> Ter) -> [(Ident,Exp)] -> Resolver Ter -> Resolver Ter
binds f = flip $ foldr $ bind f

resolveApps :: Exp -> [Exp] -> Resolver Ter
resolveApps x xs = mkApps <$> resolveExp x <*> mapM resolveExp xs

resolveExp :: Exp -> Resolver Ter
resolveExp e = case e of
  U             -> return CTT.U
  Var x         -> resolveVar x
  App t s       -> resolveApps x xs
    where (x,xs) = unApps t [s]
  Sigma ptele b -> do
    tele <- flattenPTele ptele
    binds CTT.Sigma tele (resolveExp b)
  Pi ptele b    -> do
    tele <- flattenPTele ptele
    binds CTT.Pi tele (resolveExp b)
  Fun a b       -> bind CTT.Pi ("_",a) (resolveExp b)
  Lam ptele t   -> do
    tele <- flattenPTele ptele
    lams tele (resolveExp t)
  Fst t         -> CTT.Fst <$> resolveExp t
  Snd t         -> CTT.Snd <$> resolveExp t
  Pair t0 ts    -> do
    e  <- resolveExp t0
    es <- mapM resolveExp ts
    return $ foldr1 CTT.Pair (e:es)
  Let decls e   -> do
    (rdecls,names) <- resolveDecls decls
    mkWheres rdecls <$> local (insertIdents names) (resolveExp e)
  Path is e     -> paths is (resolveExp e)
  Hole (HoleIdent (l,_)) -> CTT.Hole <$> getLoc l
  AppFormula e phi ->
    let (x,xs) = unApps e []
    in case x of
      PCon n a ->
        CTT.PCon (unAIdent n) <$> resolveExp a <*> mapM resolveExp xs
                              <*> resolveFormula phi
      _ -> CTT.AppFormula <$> resolveExp e <*> resolveFormula phi
  Trans x y   -> CTT.Trans <$> resolveExp x <*> resolveExp y
  IdP x y z   -> CTT.IdP <$> resolveExp x <*> resolveExp y <*> resolveExp z
  Comp u v ts -> CTT.Comp <$> resolveExp u <*> resolveExp v <*> resolveSystem ts
  Glue u ts   -> do
    rs <- resolveSystem ts
    let isIso (CTT.Pair _ (CTT.Pair _ (CTT.Pair _ (CTT.Pair _ _)))) = True
        isIso _ = False
    unless (all isIso $ Map.elems rs)
      (throwError $ "Not a system of isomorphisms: " ++ show rs)
    CTT.Glue <$> resolveExp u <*> pure rs
  GlueElem u ts      -> CTT.GlueElem <$> resolveExp u <*> resolveSystem ts
  CompElem a es t ts -> CTT.CompElem <$> resolveExp a <*> resolveSystem es
                                     <*> resolveExp t <*> resolveSystem ts
  ElimComp a es t    -> CTT.ElimComp <$> resolveExp a <*> resolveSystem es <*> resolveExp t
  _ -> do
    modName <- asks envModule
    throwError ("Could not resolve " ++ show e ++ " in module " ++ modName)

resolveWhere :: ExpWhere -> Resolver Ter
resolveWhere = resolveExp . unWhere

resolveSystem :: System -> Resolver (C.System Ter)
resolveSystem (System ts) =
  -- Note: the symbols in alpha are in scope in u, but they mean 0 or 1
  Map.fromList <$> sequence [ (,) <$> resolveFace alpha <*> resolveExp u
                            | Side alpha u <- ts ]

resolveFace :: [Face] -> Resolver C.Face
resolveFace alpha =
  Map.fromList <$> sequence [ (,) <$> resolveName i <*> resolveDir d
                            | Face i d <- alpha ]

resolveDir :: Dir -> Resolver C.Dir
resolveDir Dir0 = return 0
resolveDir Dir1 = return 1

resolveFormula :: Formula -> Resolver C.Formula
resolveFormula (Dir d)          = C.Dir <$> resolveDir d
resolveFormula (Atom i)         = C.Atom <$> resolveName i
resolveFormula (Neg phi)        = negFormula <$> resolveFormula phi
resolveFormula (Conj phi _ psi) =
    andFormula <$> resolveFormula phi <*> resolveFormula psi
resolveFormula (Disj phi psi)   =
    orFormula <$> resolveFormula phi <*> resolveFormula psi

resolveBranch :: Branch -> Resolver CTT.Branch
resolveBranch (OBranch (AIdent (_,lbl)) args e) = do
  re <- local (insertAIdents args) $ resolveWhere e
  return $ CTT.OBranch lbl (map unAIdent args) re
resolveBranch (PBranch (AIdent (_,lbl)) args i e) = do
  re <- local (insertName i . insertAIdents args) $ resolveWhere e
  return $ CTT.PBranch lbl (map unAIdent args) (C.Name (unAIdent i)) re

resolveTele :: [(Ident,Exp)] -> Resolver CTT.Tele
resolveTele []        = return []
resolveTele ((i,d):t) =
  ((i,) <$> resolveExp d) <:> local (insertVar i) (resolveTele t)

resolveLabel :: [(Ident,SymKind)] -> Label -> Resolver CTT.Label
resolveLabel _ (OLabel n vdecl) =
  CTT.OLabel (unAIdent n) <$> resolveTele (flattenTele vdecl)
resolveLabel cs (PLabel n vdecl t0 t1) = do
  let tele' = flattenTele vdecl
      ts = map fst tele'
  CTT.PLabel (unAIdent n) <$> resolveTele tele'
                          <*> local (insertIdents cs . insertVars ts) (resolveExp t0)
                          <*> local (insertIdents cs . insertVars ts) (resolveExp t1)

-- Resolve Data or Def or Split declarations
resolveDecl :: Decl -> Resolver (CTT.Decl,[(Ident,SymKind)])
resolveDecl d = case d of
  DeclDef (AIdent (_,f)) tele t body -> do
    let tele' = flattenTele tele
    a <- binds CTT.Pi tele' (resolveExp t)
    d <- lams tele' (local (insertVar f) $ resolveWhere body)
    return ((f,(a,d)),[(f,Variable)])
  DeclData (AIdent (l,f)) tele sums -> do
    let tele' = flattenTele tele
    a <- binds CTT.Pi tele' (return CTT.U)
    let cs  = [ (unAIdent lbl,Constructor) | OLabel lbl _ <- sums ]
    d <- lams tele' $ local (insertVar f) $
            CTT.Sum <$> getLoc l <*> pure f <*> mapM (resolveLabel cs) sums
    let pcs = [ (unAIdent lbl,PConstructor) | PLabel lbl _ _ _ <- sums ]
    return ((f,(a,d)),(f,Variable):cs ++ pcs)
  DeclSplit (AIdent (l,f)) tele t brs -> do
    let tele' = flattenTele tele
        vars = map fst tele'
    loc  <- getLoc l
    a    <- binds CTT.Pi tele' (resolveExp t)
    ty   <- local (insertVars vars) $ resolveExp t
    brs' <- local (insertVars (f:vars)) (mapM resolveBranch brs)
    body <- lams tele' (return $ CTT.Split f loc ty brs')
    return ((f,(a,body)),[(f,Variable)])
  DeclUndef (AIdent (l,f)) tele t -> do
    let tele' = flattenTele tele
    a <- binds CTT.Pi tele' (resolveExp t)
    d <- CTT.Undef <$> getLoc l <*> pure a
    return ((f,(a,d)),[(f,Variable)])

resolveDecls :: [Decl] -> Resolver ([[CTT.Decl]],[(Ident,SymKind)])
resolveDecls []     = return ([],[])
resolveDecls (d:ds) = do
  (rtd,names)  <- resolveDecl d
  (rds,names') <- local (insertIdents names) $ resolveDecls ds
  return ([rtd] : rds, names' ++ names)

resolveModule :: Module -> Resolver ([[CTT.Decl]],[(Ident,SymKind)])
resolveModule (Module (AIdent (_,n)) _ decls) =
  local (updateModule n) $ resolveDecls decls

resolveModules :: [Module] -> Resolver ([[CTT.Decl]],[(Ident,SymKind)])
resolveModules []         = return ([],[])
resolveModules (mod:mods) = do
  (rmod, names)  <- resolveModule mod
  (rmods,names') <- local (insertIdents names) $ resolveModules mods
  return (rmod ++ rmods, names' ++ names)
