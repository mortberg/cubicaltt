{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module CTT where

import Control.Applicative
import Data.List
import Data.Maybe

import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Prettyprint.Doc hiding ((<+>))
import Data.Text.Prettyprint.Doc.Render.Text

import Data.Set (Set)
import qualified Data.Set as Set
import Prelude hiding ((<>))

import Connections

--------------------------------------------------------------------------------
-- | Terms

data Loc = Loc { locFile :: String
               , locPos  :: (Int,Int) }
  deriving (Show,Eq)

type Ident  = String
type LIdent = String

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Ident,Ter)]

data Label = OLabel LIdent Tele -- Object label
           | PLabel LIdent Tele [Name] (System Ter) -- Path label
  deriving (Eq,Show)

-- OBranch of the form: c x1 .. xn -> e
-- PBranch of the form: c x1 .. xn i1 .. im -> e
data Branch = OBranch LIdent [Ident] Ter
            | PBranch LIdent [Ident] [Name] Ter
  deriving (Eq,Show)

-- Declarations: x : A = e
-- A group of mutual declarations is identified by its location. It is used to
-- speed up the Eq instance for Ctxt.
type Decl  = (Ident,(Ter,Ter))
data Decls = MutualDecls Loc [Decl]
           | OpaqueDecl Ident
           | TransparentDecl Ident
           | TransparentAllDecl
           deriving (Show,Eq)

declIdents :: [Decl] -> [Ident]
declIdents decls = [ x | (x,_) <- decls ]

declTers :: [Decl] -> [Ter]
declTers decls = [ d | (_,(_,d)) <- decls ]

declTele :: [Decl] -> Tele
declTele decls = [ (x,t) | (x,(t,_)) <- decls ]

declDefs :: [Decl] -> [(Ident,Ter)]
declDefs decls = [ (x,d) | (x,(_,d)) <- decls ]

labelTele :: Label -> (LIdent,Tele)
labelTele (OLabel c ts) = (c,ts)
labelTele (PLabel c ts _ _) = (c,ts)

labelName :: Label -> LIdent
labelName = fst . labelTele

labelTeles :: [Label] -> [(LIdent,Tele)]
labelTeles = map labelTele

lookupLabel :: LIdent -> [Label] -> Maybe Tele
lookupLabel x xs = lookup x (labelTeles xs)

lookupPLabel :: LIdent -> [Label] -> Maybe (Tele,[Name],System Ter)
lookupPLabel x xs = listToMaybe [ (ts,is,es) | PLabel y ts is es <- xs, x == y ]

branchName :: Branch -> LIdent
branchName (OBranch c _ _) = c
branchName (PBranch c _ _ _) = c

lookupBranch :: LIdent -> [Branch] -> Maybe Branch
lookupBranch _ []      = Nothing
lookupBranch x (b:brs) = case b of
  OBranch c _ _   | x == c    -> Just b
                  | otherwise -> lookupBranch x brs
  PBranch c _ _ _ | x == c    -> Just b
                  | otherwise -> lookupBranch x brs

-- Terms
data Ter = Pi Ter
         | App Ter Ter
         | Lam Ident Ter Ter
         | Where Ter Decls
         | Var Ident
         | U
           -- Sigma types:
         | Sigma Ter
         | Pair Ter Ter
         | Fst Ter
         | Snd Ter
           -- constructor c Ms
         | Con LIdent [Ter]
         | PCon LIdent Ter [Ter] [Formula] -- c A ts phis (A is the data type)
           -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Ident Loc Ter [Branch]
           -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Loc Ident [Label] -- TODO: should only contain OLabels
         | HSum Loc Ident [Label]
           -- undefined and holes
         | Undef Loc Ter -- Location and type
         | Hole Loc
           -- Path types
         | PathP Ter Ter Ter
         | PLam Name Ter
         | AppFormula Ter Formula
           -- Homogeneous Kan composition and filling
         | HComp Ter Ter (System Ter)
         | HFill Ter Ter (System Ter)
           -- Generalized transports
         | Trans Ter Formula Ter
         -- TODO?: TransFill Ter Formula Ter
           -- Heterogeneous Kan composition and filling
         | Comp Ter Ter (System Ter)
         | Fill Ter Ter (System Ter)
           -- Glue
         | Glue Ter (System Ter)
         | GlueElem Ter (System Ter)
         | UnGlueElem Ter Ter (System Ter)
           -- Id
         | Id Ter Ter Ter
         | IdPair Ter (System Ter)
         | IdJ Ter Ter Ter Ter Ter Ter
  deriving (Show,Eq)

-- For an expression t, returns (u,ts) where u is no application and t = u ts
unApps :: Ter -> (Ter,[Ter])
unApps = aux []
  where aux :: [Ter] -> Ter -> (Ter,[Ter])
        aux acc (App r s) = aux (s:acc) r
        aux acc t         = (t,acc)

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

mkWheres :: [Decls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

--------------------------------------------------------------------------------
-- | Values

data Val = VU
         | Ter Ter Env
         | VPi Val Val
         | VSigma Val Val
         | VPair Val Val
         | VCon LIdent [Val]
         | VPCon LIdent Val [Val] [Formula]

           -- Path values
         | VPathP Val Val Val
         | VPLam Name Val

           -- Glue values
         | VGlue Val (System Val)
         | VGlueElem Val (System Val)        -- glue a [ phi -> t ]
         | VUnGlueElem Val Val (System Val)  -- unglue u A [phi -> (T,w)]

           -- Composition in the universe
         | VHCompU Val (System Val)

           -- Composition; the type is not constant
         | VComp Val Val (System Val)

           -- Homogeneous composition; the type is constant. The Name is bound in the tubes
         | VHComp Name Val Val (System Val)

           -- Generalized transport
         | VTrans Val Formula Val

           -- Id
         | VId Val Val Val
         | VIdPair Val (System Val)

           -- Neutral values:
         | VVar Ident Val
         | VOpaque Ident Val
         | VFst Val
         | VSnd Val
         | VSplit Val Val
         | VApp Val Val
         | VAppFormula Val Formula
         | VLam Ident Val Val
         | VUnGlueElemU Val Val (System Val)
         | VIdJ Val Val Val Val Val Val
  deriving Eq

isNeutral :: Val -> Bool
isNeutral v = case v of
  Ter Undef{} _  -> True
  Ter Hole{} _   -> True
  VVar{}         -> True
  VOpaque{}      -> True
  VHComp{}       -> True
  VComp{}       -> True  
  VTrans{}       -> True
  VFst{}         -> True
  VSnd{}         -> True
  VSplit{}       -> True
  VApp{}         -> True
  VAppFormula{}  -> True
  VUnGlueElemU{} -> True
  VUnGlueElem{}  -> True
  VIdJ{}         -> True
  _              -> False

isNeutralSystem :: System Val -> Bool
isNeutralSystem = any isNeutral . elems

-- isNeutralPath :: Val -> Bool
-- isNeutralPath (VPath _ v) = isNeutral v
-- isNeutralPath _ = True

mkVar :: Int -> String -> Val -> Val
mkVar k x = VVar (x ++ show k)

mkVarNice :: [String] -> String -> Val -> Val
mkVarNice xs x = VVar (head (ys \\ xs))
  where ys = x:map (\n -> x ++ show n) [0..]

unCon :: Val -> [Val]
unCon (VCon _ vs) = vs
unCon v           = error $ "unCon: not a constructor: " ++ show (showVal v)

isCon :: Val -> Bool
isCon VCon{} = True
isCon _      = False

-- Constant path: <_> v
constPath :: Val -> Val
constPath = VPLam (Name "_")

-- Check if a function is non-dependent
isNonDep :: Val -> Bool
isNonDep (Ter (Lam "_" _ _) _) = True
isNonDep _ = False

--------------------------------------------------------------------------------
-- | Environments

data Ctxt = Empty
          | Upd Ident Ctxt
          | Sub Name Ctxt
          | Def Loc [Decl] Ctxt

instance Eq Ctxt where
    c == d = case (c, d) of
        (Empty, Empty)              -> True
        (Upd x c', Upd y d')        -> x == y && c' == d'
        (Sub i c', Sub j d')        -> i == j && c' == d'
        (Def m xs c', Def n ys d')  -> (m == n || xs == ys) && c' == d'
            -- Invariant: if two declaration groups come from the same
            -- location, they are equal and their contents are not compared.
        _                           -> False

-- The Idents and Names in the Ctxt refer to the elements in the two
-- lists. This is more efficient because acting on an environment now
-- only need to affect the lists and not the whole context.
-- The last list is the list of opaque names
newtype Env = Env (Ctxt,[Val],[Formula],Nameless (Set Ident))
  deriving (Eq)

emptyEnv :: Env
emptyEnv = Env (Empty,[],[],Nameless Set.empty)

def :: Decls -> Env -> Env
def (MutualDecls m ds) (Env (rho,vs,fs,Nameless os)) = Env (Def m ds rho,vs,fs,Nameless (os Set.\\ Set.fromList (declIdents ds)))
def (OpaqueDecl n) (Env (rho,vs,fs,Nameless os)) = Env (rho,vs,fs,Nameless (Set.insert n os))
def (TransparentDecl n) (Env (rho,vs,fs,Nameless os)) = Env (rho,vs,fs,Nameless (Set.delete n os))
def TransparentAllDecl (Env (rho,vs,fs,Nameless os)) = Env (rho,vs,fs,Nameless Set.empty)

defWhere :: Decls -> Env -> Env
defWhere (MutualDecls m ds) (Env (rho,vs,fs,Nameless os)) = Env (Def m ds rho,vs,fs,Nameless (os Set.\\ Set.fromList (declIdents ds)))
defWhere (OpaqueDecl _) rho = rho
defWhere (TransparentDecl _) rho = rho
defWhere TransparentAllDecl rho = rho

sub :: (Name,Formula) -> Env -> Env
sub (i,phi) (Env (rho,vs,fs,os)) = Env (Sub i rho,vs,phi:fs,os)

upd :: (Ident,Val) -> Env -> Env
upd (x,v) (Env (rho,vs,fs,Nameless os)) = Env (Upd x rho,v:vs,fs,Nameless (Set.delete x os))

upds :: [(Ident,Val)] -> Env -> Env
upds xus rho = foldl (flip upd) rho xus

updsTele :: Tele -> [Val] -> Env -> Env
updsTele tele vs = upds (zip (map fst tele) vs)

subs :: [(Name,Formula)] -> Env -> Env
subs iphis rho = foldl (flip sub) rho iphis

mapEnv :: (Val -> Val) -> (Formula -> Formula) -> Env -> Env
mapEnv f g (Env (rho,vs,fs,os)) = Env (rho,map f vs,map g fs,os)

valAndFormulaOfEnv :: Env -> ([Val],[Formula])
valAndFormulaOfEnv (Env (_,vs,fs,_)) = (vs,fs)

valOfEnv :: Env -> [Val]
valOfEnv = fst . valAndFormulaOfEnv

formulaOfEnv :: Env -> [Formula]
formulaOfEnv = snd . valAndFormulaOfEnv

domainEnv :: Env -> [Name]
domainEnv (Env (rho,_,_,_)) = domCtxt rho
  where domCtxt rho = case rho of
          Empty      -> []
          Upd _ e    -> domCtxt e
          Def _ ts e -> domCtxt e
          Sub i e    -> i : domCtxt e

-- Extract the context from the environment, used when printing holes
contextOfEnv :: Env -> [String]
contextOfEnv rho = case rho of
  Env (Empty,_,_,_)               -> []
  Env (Upd x e,VVar n t:vs,fs,os) -> (n ++ " : " ++ show (showVal t)) : contextOfEnv (Env (e,vs,fs,os))
  Env (Upd x e,v:vs,fs,os)        -> (x ++ " = " ++ show (showVal v)) : contextOfEnv (Env (e,vs,fs,os))
  Env (Def _ _ e,vs,fs,os)        -> contextOfEnv (Env (e,vs,fs,os))
  Env (Sub i e,vs,phi:fs,os)      -> (show i ++ " = " ++ show phi) : contextOfEnv (Env (e,vs,fs,os))

--------------------------------------------------------------------------------
-- | Pretty printing

-- instance Show Env where
--   show = render . showEnv True

(<+>) :: Doc ann -> Doc ann -> Doc ann
x <+> y | show x == "" = y
        | show y == "" = x
        | otherwise = x <> space <> y

showEnv :: Bool -> Env -> Doc a
showEnv b e =
  let -- This decides if we should print "x = " or not
      names x = if b then pretty x <+> equals else emptyDoc
      par   x = if b then parens x else x
      com     = if b then comma else emptyDoc
      showEnv1 e = case e of
        Env (Upd x env,u:us,fs,os)   ->
          showEnv1 (Env (env,us,fs,os)) <+> names x <+> showVal1 u <> com
        Env (Sub i env,us,phi:fs,os) ->
          showEnv1 (Env (env,us,fs,os)) <+> names (show i) <+> pretty (show phi) <> com
        Env (Def _ _ env,vs,fs,os)   -> showEnv1 (Env (env,vs,fs,os))
        _                            -> showEnv b e
  in case e of
    Env (Empty,_,_,_)            -> emptyDoc
    Env (Def _ _ env,vs,fs,os)   -> showEnv b (Env (env,vs,fs,os))
    Env (Upd x env,u:us,fs,os)   ->
      par $ showEnv1 (Env (env,us,fs,os)) <+> names x <+> showVal1 u
    Env (Sub i env,us,phi:fs,os) ->
      par $ showEnv1 (Env (env,us,fs,os)) <+> names (show i) <+> pretty (show phi)

-- instance Show Loc where
--   show = render . showLoc

showLoc :: Loc -> Doc a
showLoc (Loc name (i,j)) = pretty (i,j) <+> pretty "in" <+> pretty name

showFormula :: Formula -> Doc a
showFormula phi = case phi of
  _ :\/: _ -> parens (pretty (show phi))
  _ :/\: _ -> parens (pretty (show phi))
  _ -> pretty $ show phi

-- instance Show Ter where
--   show = render . showTer

showSystem :: (a -> Doc b) -> System a -> Doc b
showSystem f (Sys x) = showListSystem f x

-- Use align here instead of hsep to get prettier printing
showListSystem :: (a -> Doc b) -> [(Face,a)] -> Doc b
showListSystem f [] = lbracket <> rbracket
showListSystem f ts =
  lbracket <> hsep (punctuate comma (map (\(alpha,u) -> pretty (showFace alpha) <+> pretty "->" <+> f u) ts)) <> rbracket

showTer :: Ter -> Doc a
showTer v = case v of
  U                  -> pretty 'U'
  App e0 e1          -> showTer e0 <+> showTer1 e1
  Pi e0              -> pretty "Pi" <+> showTer e0
  Lam x t e          -> pretty '\\' <> parens (pretty x <+> colon <+> showTer t) <+>
                          pretty "->" <+> showTer e
  Fst e              -> showTer1 e <> pretty ".1"
  Snd e              -> showTer1 e <> pretty ".2"
  Sigma e0           -> pretty "Sigma" <+> showTer1 e0
  Pair e0 e1         -> parens (showTer e0 <> comma <> showTer e1)
  Where e d          -> showTer e <+> pretty "where" <+> showDecls d
  Var x              -> pretty x
  Con c es           -> pretty c <+> showTers es
  PCon c a es phis   -> pretty c <+> braces (showTer a) <+> showTers es
                        <+> hsep (map ((pretty '@' <+>) . showFormula) phis)
  Split f _ _ _      -> pretty f
  Sum _ n _          -> pretty n
  HSum _ n _         -> pretty n
  Undef{}            -> pretty "undefined"
  Hole{}             -> pretty "?"
  PathP e0 e1 e2     -> pretty "PathP" <+> showTers [e0,e1,e2]
  PLam i e           -> pretty '<' <> pretty (show i) <> pretty '>' <+> showTer e
  AppFormula e phi   -> showTer1 e <+> pretty '@' <+> showFormula phi
  HComp a t ts       -> pretty "hcomp" <+> showTers [a,t] <+> showSystem showTer ts
  HFill a t ts       -> pretty "hfill" <+> showTers [a,t] <+> showSystem showTer ts
  Trans e phi t0     -> pretty "transGen" <+> showTer1 e <+> showFormula phi
                        <+> showTer1 t0
  Comp e t ts        -> pretty "comp" <+> showTers [e,t] <+> showSystem showTer ts
  Fill e t ts        -> pretty "fill" <+> showTers [e,t] <+> showSystem showTer ts
  Glue a ts          -> pretty "Glue" <+> showTer1 a <+> showSystem showTer ts
  GlueElem a ts      -> pretty "glue" <+> showTer1 a <+> showSystem showTer ts
  UnGlueElem a b ts  -> pretty "unglue" <+> showTers [a,b] <+> showSystem showTer ts
  Id a u v           -> pretty "Id" <+> showTers [a,u,v]
  IdPair b ts        -> pretty "idC" <+> showTer1 b <+> showSystem showTer ts
  IdJ a t c d x p    -> pretty "idJ" <+> showTers [a,t,c,d,x,p]

showTers :: [Ter] -> Doc a
showTers = hsep . map showTer1

showTer1 :: Ter -> Doc a
showTer1 t = case t of
  U        -> pretty 'U'
  Con c [] -> pretty c
  Var{}    -> showTer t
  Undef{}  -> showTer t
  Hole{}   -> showTer t
  Split{}  -> showTer t
  Sum{}    -> showTer t
  HSum{}   -> showTer t
  Fst{}    -> showTer t
  Snd{}    -> showTer t
  _        -> parens (showTer t)

showDecls :: Decls -> Doc a
showDecls (MutualDecls _ defs) =
  hsep $ punctuate comma
  [ pretty x <+> equals <+> showTer d | (x,(_,d)) <- defs ]
showDecls (OpaqueDecl i) = pretty "opaque" <+> pretty i
showDecls (TransparentDecl i) = pretty "transparent" <+> pretty i
showDecls TransparentAllDecl = pretty "transparent_all"

-- instance Show Val where
--   show = render . showVal

showVal :: Val -> Doc a
showVal v = case v of
  VU                -> pretty 'U'
  Ter t@Sum{} rho   -> showTer t <+> showEnv False rho
  Ter t@HSum{} rho  -> showTer t <+> showEnv False rho
  Ter t@Split{} rho -> showTer t <+> showEnv False rho
  Ter t rho         -> showTer1 t <+> showEnv True rho
  VCon c us         -> pretty c <+> showVals us
  VPCon c a us phis -> pretty c <+> braces (showVal a) <+> showVals us
                       <+> hsep (map ((pretty '@' <+>) . showFormula) phis)
  VHComp i v0 v1 vs   -> pretty "hcomp" <+> showVals [v0,v1] <+> showSystem showVal (mapSystem (VPLam i) vs)
  VComp v0 v1 vs    -> pretty "comp" <+> showVals [v0,v1] <+> showSystem showVal vs
  VTrans u phi v0   -> pretty "transGen" <+> showVal1 u <+> showFormula phi
                       <+> showVal1 v0
  VPi a l@(VLam x t b)
  -- TODO
--    | "_" `isPrefixOf` x -> showVal1 a <+> pretty "->" <+> showVal1 b
    | otherwise          -> pretty '(' <> showLam v
  VPi a b           -> pretty "Pi" <+> showVals [a,b]
  VPair u v         -> parens (showVal u <> comma <> showVal v)
  VSigma u v        -> pretty "Sigma" <+> showVals [u,v]
  VApp u v          -> showVal u <+> showVal1 v
  VLam{}            -> pretty "\\(" <> showLam v
  VPLam{}           -> pretty '<' <> showPLam v
  VSplit u v        -> showVal u <+> showVal1 v
  VVar x _          -> pretty x
  VOpaque x _       -> pretty '#' <+> pretty x
  VFst u            -> showVal1 u <> pretty ".1"
  VSnd u            -> showVal1 u <> pretty ".2"
  VPathP v0 v1 v2   -> pretty "PathP" <+> showVals [v0,v1,v2]
  VAppFormula v phi -> showVal v <+> pretty '@' <+> showFormula phi
  VGlue a ts        -> pretty "Glue" <+> showVal1 a <+> showSystem showVal ts
  VGlueElem a ts    -> pretty "glue" <+> showVal1 a <+> showSystem showVal ts
  VUnGlueElem v a ts  -> pretty "unglue" <+> showVals [v,a] <+> showSystem showVal ts
  VUnGlueElemU v b es -> pretty "unglue U" <+> showVals [v,b]
                         <+> showSystem showVal es
  VHCompU a ts        -> pretty "hcomp U" <+> showVal1 a <+> showSystem showVal ts
  VId a u v           -> pretty "Id" <+> showVals [a,u,v]
  VIdPair b ts        -> pretty "idC" <+> showVal1 b <+> showSystem showVal ts
  VIdJ a t c d x p    -> pretty "idJ" <+> showVals [a,t,c,d,x,p]

showPLam :: Val -> Doc a
showPLam e = case e of
  VPLam i a@VPLam{} -> pretty (show i) <+> showPLam a
  VPLam i a         -> pretty (show i) <> pretty '>' <+> showVal a
  _                 -> showVal e

-- Merge lambdas of the same type
showLam :: Val -> Doc a
showLam e = case e of
  VLam x t a@(VLam _ t' _)
    | t == t'   -> pretty x <+> showLam a
    | otherwise ->
      pretty x <+> colon <+> showVal t <> pretty ')' <+> pretty "->" <+> showVal a
  VPi _ (VLam x t a@(VPi _ (VLam _ t' _)))
    | t == t'   -> pretty x <+> showLam a
    | otherwise ->
      pretty x <+> colon <+> showVal t <> pretty ')' <+> pretty "->" <+> showVal a
  VLam x t e         ->
    pretty x <+> colon <+> showVal t <> pretty ')' <+> pretty "->" <+> showVal e
  VPi _ (VLam x t e) ->
    pretty x <+> colon <+> showVal t <> pretty ')' <+> pretty "->" <+> showVal e
  _ -> showVal e

showVal1 :: Val -> Doc a
showVal1 v = case v of
  VU                -> showVal v
  VCon c []         -> showVal v
  VVar{}            -> showVal v
  VFst{}            -> showVal v
  VSnd{}            -> showVal v
  Ter t rho | show (showEnv False rho) == "" -> showTer1 t
  _                 -> parens (showVal v)

showVals :: [Val] -> Doc a
showVals = hsep . map showVal1


-------------------------------------------------------------------------------

countHComps :: [Val] -> Int
countHComps = sum . map countHComp

countHCompSystem :: System Val -> Int
countHCompSystem = countHComps . elems

countHComp :: Val -> Int
countHComp v = case v of
  VU                -> 0
  Ter t rho         -> 0
  VCon c us         -> countHComps us
  VPCon c a us phis -> countHComp a + countHComps us
  VHComp _ v0 v1 vs   -> 1 + countHComps [v0,v1] + countHCompSystem vs
  VComp v0 v1 vs    -> countHComps [v0,v1] + countHCompSystem vs
  VTrans u phi v0   -> countHComps [u,v0]
  VPi a l@(VLam x t b) -> countHComps [a,t,b]
  VPi a b           -> countHComps [a,b]
  VPair u v         -> countHComps [u,v]
  VSigma u v        -> countHComps [u,v]
  VApp u v          -> countHComps [u,v]
  VLam x t b        -> countHComps [t,b]
  VPLam i b         -> countHComp b
  VSplit u v        -> countHComps [u,v]
  VVar x _          -> 0
  VOpaque x _       -> 0
  VFst u            -> countHComp u
  VSnd u            -> countHComp u
  VPathP v0 v1 v2   -> countHComps [v0,v1,v2]
  VAppFormula v phi -> countHComp v
  VGlue a ts        -> countHComp a + countHCompSystem ts
  VGlueElem a ts    -> countHComp a + countHCompSystem ts
  VUnGlueElem v a ts  -> countHComps [v,a] + countHCompSystem ts
  VUnGlueElemU v b es -> countHComps [v,b] + countHCompSystem es
  VHCompU a ts        -> countHComp a + countHCompSystem ts
  VId a u v           -> countHComps [a,u,v]
  VIdPair b ts        -> countHComp b + countHCompSystem ts
  VIdJ a t c d x p    -> countHComps [a,t,c,d,x,p]
  foo -> error ("countHComp " ++ show (showVal foo))
