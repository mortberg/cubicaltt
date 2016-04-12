{-# LANGUAGE TupleSections #-}

-- | Convert the concrete syntax into the syntax of cubical TT.
module Resolver where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Identity
import Data.List
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

-- Transform a sequence of applications
-- (((u v1) .. vn) phi1) .. phim into (u,[v1,..,vn],[phi1,..,phim])
unAppsFormulas :: Exp -> [Formula]-> (Exp,[Exp],[Formula])
unAppsFormulas (AppFormula u phi) phis = unAppsFormulas u (phi:phis)
unAppsFormulas u phis = (x,xs,phis)
  where (x,xs) = unApps u []

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

insertNames :: [AIdent] -> Env -> Env
insertNames = flip $ foldr insertName

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
    Just PConstructor ->
      throwError $ "The path constructor " ++ x ++ " is used as a" ++
                   " variable at " ++ show l ++ " in " ++ modName ++
                   " (path constructors should have their type in" ++
                   " curly braces as first argument)"
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
paths [] _ = throwError "Empty path abstraction"
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
  AppFormula t phi ->
    let (x,xs,phis) = unAppsFormulas e []
    in case x of
      PCon n a ->
        CTT.PCon (unAIdent n) <$> resolveExp a <*> mapM resolveExp xs
                              <*> mapM resolveFormula phis
      _ -> CTT.AppFormula <$> resolveExp t <*> resolveFormula phi
  IdP a u v     -> CTT.IdP <$> resolveExp a <*> resolveExp u <*> resolveExp v
  Comp u v ts   -> CTT.Comp <$> resolveExp u <*> resolveExp v <*> resolveSystem ts
  Fill u v ts   -> CTT.Fill <$> resolveExp u <*> resolveExp v <*> resolveSystem ts
  Trans u v     -> CTT.Comp <$> resolveExp u <*> resolveExp v <*> pure Map.empty
  Glue u ts     -> CTT.Glue <$> resolveExp u <*> resolveSystem ts
  GlueElem u ts -> CTT.GlueElem <$> resolveExp u <*> resolveSystem ts
  UnGlueElem u ts -> CTT.UnGlueElem <$> resolveExp u <*> resolveSystem ts
  _ -> do
    modName <- asks envModule
    throwError ("Could not resolve " ++ show e ++ " in module " ++ modName)

resolveWhere :: ExpWhere -> Resolver Ter
resolveWhere = resolveExp . unWhere

resolveSystem :: System -> Resolver (C.System Ter)
resolveSystem (System ts) = do
  ts' <- sequence [ (,) <$> resolveFace alpha <*> resolveExp u
                  | Side alpha u <- ts ]
  let alphas = map fst ts'
  unless (nub alphas == alphas) $
    throwError $ "system contains same face multiple times: " ++
                 C.showListSystem ts'
  -- Note: the symbols in alpha are in scope in u, but they mean 0 or 1
  return $ Map.fromList ts'

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
resolveBranch (PBranch (AIdent (_,lbl)) args is e) = do
  re <- local (insertNames is . insertAIdents args) $ resolveWhere e
  let names = map (C.Name . unAIdent) is
  return $ CTT.PBranch lbl (map unAIdent args) names re

resolveTele :: [(Ident,Exp)] -> Resolver CTT.Tele
resolveTele []        = return []
resolveTele ((i,d):t) =
  ((i,) <$> resolveExp d) <:> local (insertVar i) (resolveTele t)

resolveLabel :: [(Ident,SymKind)] -> Label -> Resolver CTT.Label
resolveLabel _ (OLabel n vdecl) =
  CTT.OLabel (unAIdent n) <$> resolveTele (flattenTele vdecl)
resolveLabel cs (PLabel n vdecl is sys) = do
  let tele' = flattenTele vdecl
      ts    = map fst tele'
      names = map (C.Name . unAIdent) is
      n'    = unAIdent n
      cs'   = delete (n',PConstructor) cs
  CTT.PLabel n' <$> resolveTele tele' <*> pure names
                <*> local (insertNames is . insertIdents cs' . insertVars ts)
                      (resolveSystem sys)

-- Resolve a non-mutual declaration; returns resolver for type and
-- body separately
resolveNonMutualDecl :: Decl -> (Ident,Resolver CTT.Ter
                                ,Resolver CTT.Ter,[(Ident,SymKind)])
resolveNonMutualDecl d = case d of
  DeclDef (AIdent (_,f)) tele t body ->
    let tele' = flattenTele tele
        a     = binds CTT.Pi tele' (resolveExp t)
        d     = lams tele' (local (insertVar f) $ resolveWhere body)
    in (f,a,d,[(f,Variable)])
  DeclData x tele sums  -> resolveDeclData x tele sums null
  DeclHData x tele sums ->
    resolveDeclData x tele sums (const False) -- always pick HSum
  DeclSplit (AIdent (l,f)) tele t brs ->
    let tele' = flattenTele tele
        vars  = map fst tele'
        a     = binds CTT.Pi tele' (resolveExp t)
        d     = do
                  loc <- getLoc l
                  ty  <- local (insertVars vars) $ resolveExp t
                  brs' <- local (insertVars (f:vars)) (mapM resolveBranch brs)
                  lams tele' (return $ CTT.Split f loc ty brs')
    in (f,a,d,[(f,Variable)])
  DeclUndef (AIdent (l,f)) tele t ->
    let tele' = flattenTele tele
        a     = binds CTT.Pi tele' (resolveExp t)
        d     = CTT.Undef <$> getLoc l <*> a
    in (f,a,d,[(f,Variable)])

-- Helper function to resolve data declarations. The predicate p is
-- used to decide if we should use Sum or HSum.
resolveDeclData :: AIdent -> [Tele] -> [Label] -> ([(Ident,SymKind)] -> Bool) ->
                   (Ident, Resolver Ter, Resolver Ter, [(Ident, SymKind)])
resolveDeclData (AIdent (l,f)) tele sums p =
  let tele' = flattenTele tele
      a     = binds CTT.Pi tele' (return CTT.U)
      cs    = [ (unAIdent lbl,Constructor) | OLabel lbl _ <- sums ]
      pcs   = [ (unAIdent lbl,PConstructor) | PLabel lbl _ _ _ <- sums ]
      sum   = if p pcs then CTT.Sum else CTT.HSum
      d = lams tele' $ local (insertVar f) $
            sum <$> getLoc l <*> pure f
                <*> mapM (resolveLabel (cs ++ pcs)) sums
  in (f,a,d,(f,Variable):cs ++ pcs)

resolveRTele :: [Ident] -> [Resolver CTT.Ter] -> Resolver CTT.Tele
resolveRTele [] _ = return []
resolveRTele (i:is) (t:ts) = do
  a  <- t
  as <- local (insertVar i) (resolveRTele is ts)
  return ((i,a):as)

-- Resolve a declaration
resolveDecl :: Decl -> Resolver (CTT.Decls,[(Ident,SymKind)])
resolveDecl d = case d of
  DeclMutual decls -> do
    let (fs,ts,bs,nss) = unzip4 $ map resolveNonMutualDecl decls
        ns = concat nss -- TODO: some sanity checks? Duplicates!?
    when (nub (map fst ns) /= concatMap (map fst) nss) $
      throwError ("Duplicated constructor or ident: " ++ show nss)
    as <- resolveRTele fs ts
    -- The bodies know about all the names and constructors in the
    -- mutual block
    ds <- sequence $ map (local (insertIdents ns)) bs
    let ads = zipWith (\ (x,y) z -> (x,(y,z))) as ds
    return (CTT.MutualDecls ads,ns)
  DeclOpaque i  -> do
    resolveVar i
    return (CTT.OpaqueDecl (unAIdent i), [])
  DeclVisible i -> do
    resolveVar i
    return (CTT.VisibleDecl (unAIdent i), [])
  _ -> do let (f,typ,body,ns) = resolveNonMutualDecl d
          a <- typ
          d <- body
          return (CTT.MutualDecls [(f,(a,d))],ns)

resolveDecls :: [Decl] -> Resolver ([CTT.Decls],[(Ident,SymKind)])
resolveDecls []     = return ([],[])
resolveDecls (d:ds) = do
  (rtd,names)  <- resolveDecl d
  (rds,names') <- local (insertIdents names) $ resolveDecls ds
  return (rtd : rds, names' ++ names)

resolveModule :: Module -> Resolver ([CTT.Decls],[(Ident,SymKind)])
resolveModule (Module (AIdent (_,n)) _ decls) =
  local (updateModule n) $ resolveDecls decls

resolveModules :: [Module] -> Resolver ([CTT.Decls],[(Ident,SymKind)])
resolveModules []         = return ([],[])
resolveModules (mod:mods) = do
  (rmod, names)  <- resolveModule mod
  (rmods,names') <- local (insertIdents names) $ resolveModules mods
  return (rmod ++ rmods, names' ++ names)
