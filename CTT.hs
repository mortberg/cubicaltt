module CTT where

import Control.Applicative
import Data.List
import Data.Maybe
import Data.Map (Map,(!))
import qualified Data.Map as Map
import Text.PrettyPrint as PP

import Connections

--------------------------------------------------------------------------------
-- | Terms

data Loc = Loc { locFile :: String
               , locPos  :: (Int,Int) }
  deriving Eq

type Ident  = String
type LIdent = String

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Ident,Ter)]

data Label = OLabel LIdent Tele -- Object label
           | PLabel LIdent Tele Ter Ter -- Path label
  deriving (Eq,Show)

-- OBranch of the form: c x1 .. xn -> e
-- PBranch of the form: c x1 .. xn i -> e
data Branch = OBranch LIdent [Ident] Ter
            | PBranch LIdent [Ident] Name Ter
  deriving (Eq,Show)

-- Declarations: x : A = e
type Decl   = (Ident,(Ter,Ter))

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

lookupPLabel :: LIdent -> [Label] -> Maybe (Tele,Ter,Ter)
lookupPLabel x xs = listToMaybe [ (ts,t0,t1) | PLabel y ts t0 t1 <- xs, x == y ]

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
data Ter = App Ter Ter
         | Pi Ter
         | Lam Ident Ter Ter
         | Where Ter [Decl]
         | Var Ident
         | U
           -- Sigma types:
         | Sigma Ter
         | Pair Ter Ter
         | Fst Ter
         | Snd Ter
           -- constructor c Ms
         | Con LIdent [Ter]
         | PCon LIdent Ter [Ter] Formula -- c A ts phi (A is the data type)
           -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Ident Loc Ter [Branch]
           -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Loc Ident [Label]
           -- undefined
         | Undef Loc

           -- Id type
         | IdP Ter Ter Ter
         | Path Name Ter
         | AppFormula Ter Formula
           -- Kan Composition
         | Comp Ter Ter (System Ter)
         | Trans Ter Ter
           -- Composition in the Universe
         | CompElem Ter (System Ter) Ter (System Ter)
         | ElimComp Ter (System Ter) Ter
           -- Glue
         | Glue Ter (System Ter)
         | GlueElem Ter (System Ter)
  deriving Eq

-- For an expression t, returns (u,ts) where u is no application and t = u ts
unApps :: Ter -> (Ter,[Ter])
unApps = aux []
  where aux :: [Ter] -> Ter -> (Ter,[Ter])
        aux acc (App r s) = aux (s:acc) r
        aux acc t         = (t,acc)

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

mkWheres :: [[Decl]] -> Ter -> Ter
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
           -- The Formula is the direction of the equality in VPCon
         | VPCon LIdent Val [Val] Formula

           -- Id values
         | VIdP Val Val Val
         | VPath Name Val
         | VComp Val Val (System Val)
         | VTrans Val Val

           -- Glue values
         | VGlue Val (System Val)
         | VGlueElem Val (System Val)

           -- Universe Composition Values
         | VCompElem Val (System Val) Val (System Val)
         | VElimComp Val (System Val) Val

           -- Neutral values:
         | VVar Ident Val
         | VFst Val
         | VSnd Val
         | VSplit Val Val
         | VApp Val Val
         | VAppFormula Val Formula
  deriving Eq

isNeutral :: Val -> Bool
isNeutral v = case v of
  VVar _ _          -> True
  VFst v            -> isNeutral v
  VSnd v            -> isNeutral v
  VSplit _ v        -> isNeutral v
  VApp v _          -> isNeutral v
  VAppFormula v _   -> isNeutral v
  VComp a u ts      -> isNeutralComp a u ts
  VTrans a u        -> isNeutralTrans a u
  VCompElem _ _ u _ -> isNeutral u
  VElimComp _ _ u   -> isNeutral u
  _                 -> False

isNeutralSystem :: System Val -> Bool
isNeutralSystem = any isNeutralPath . Map.elems

isNeutralPath :: Val -> Bool
isNeutralPath (VPath _ v) = isNeutral v
isNeutralPath _ = True

isNeutralTrans :: Val -> Val -> Bool
isNeutralTrans (VPath i a) u = foo i a u
  where foo :: Name -> Val -> Val -> Bool
        foo i a u | isNeutral a = True
        foo i (Ter Sum{} _) u   = isNeutral u
        foo i (VGlue _ as) u    =
          let shasBeta = (shape as) `face` (i ~> 0)
          in shasBeta /= Map.empty && eps `Map.notMember` shasBeta && isNeutral u
isNeutralTrans u _ = isNeutral u

isNeutralComp :: Val -> Val -> System Val -> Bool
isNeutralComp a _ _ | isNeutral a = True
isNeutralComp (Ter Sum{} _) u ts  = isNeutral u || isNeutralSystem ts
isNeutralComp (VGlue _ as) u ts | isNeutral u = True
                                | otherwise   =
  let shas = shape as
      testFace beta _ = let shasBeta = shas `face` beta
                        in shasBeta /= Map.empty && eps `Map.notMember` shasBeta
  in isNeutralSystem (Map.filterWithKey testFace ts)
isNeutralComp _ _ _ = False

mkVar :: Int -> Val -> Val
mkVar k = VVar ('X' : show k)

unCon :: Val -> [Val]
unCon (VCon _ vs) = vs
unCon v           = error $ "unCon: not a constructor: " ++ show v

isCon :: Val -> Bool
isCon VCon{} = True
isCon _      = False

--------------------------------------------------------------------------------
-- | Environments

data Env = Empty
         | Upd Env (Ident,Val)
         | Def [Decl] Env
         | Sub Env (Name,Formula)
  deriving Eq

upds :: Env -> [(Ident,Val)] -> Env
upds = foldl Upd

updsTele :: Env -> Tele -> [Val] -> Env
updsTele rho tele vs = upds rho (zip (map fst tele) vs)

mapEnv :: (Val -> Val) -> (Formula -> Formula) -> Env -> Env
mapEnv f g e = case e of
  Empty         -> Empty
  Upd e (x,v)   -> Upd (mapEnv f g e) (x,f v)
  Def ts e      -> Def ts (mapEnv f g e)
  Sub e (i,phi) -> Sub (mapEnv f g e) (i,g phi)

valAndFormulaOfEnv :: Env -> ([Val],[Formula])
valAndFormulaOfEnv rho = case rho of
  Empty -> ([],[])
  Upd rho (_,u) -> let (us,phis) = valAndFormulaOfEnv rho
                   in (u:us,phis)
  Sub rho (_,phi) -> let (us,phis) = valAndFormulaOfEnv rho
                     in (us,phi:phis)
  Def _ rho -> valAndFormulaOfEnv rho

valOfEnv :: Env -> [Val]
valOfEnv = fst . valAndFormulaOfEnv

formulaOfEnv :: Env -> [Formula]
formulaOfEnv = snd . valAndFormulaOfEnv

domainEnv :: Env -> [Name]
domainEnv rho = case rho of
  Empty       -> []
  Upd e (x,v) -> domainEnv e
  Def ts e    -> domainEnv e
  Sub e (i,_) -> i : domainEnv e

--------------------------------------------------------------------------------
-- | Pretty printing

instance Show Env where
  show = render . showEnv

showEnv, showEnv1 :: Env -> Doc
showEnv e = case e of
  Empty           -> PP.empty
  Def _ env       -> showEnv env
  Upd env (x,u)   -> parens (showEnv1 env <> showVal u)
  Sub env (i,phi) -> parens (showEnv1 env <> text (show phi))
showEnv1 (Upd env (x,u)) = showEnv1 env <> showVal u <> text ", "
showEnv1 e               = showEnv e

instance Show Loc where
  show = render . showLoc

showLoc :: Loc -> Doc
showLoc (Loc name (i,j)) = hcat [text name,text "_L",int i,text "_C",int j]

showFormula :: Formula -> Doc
showFormula phi = case phi of
  _ :\/: _ -> parens (text (show phi))
  _ :/\: _ -> parens (text (show phi))
  _ -> text $ show phi

instance Show Ter where
  show = render . showTer

showTer :: Ter -> Doc
showTer v = case v of
  U                  -> char 'U'
  App e0 e1          -> showTer e0 <+> showTer1 e1
  Pi e0              -> text "Pi" <+> showTer e0
  Lam x t e          -> char '\\' <> text x <+> text "->" <+> showTer e
  Fst e              -> showTer e <> text ".1"
  Snd e              -> showTer e <> text ".2"
  Sigma e0           -> text "Sigma" <+> showTer e0
  Pair e0 e1         -> parens (showTer e0 <> comma <> showTer e1)
  Where e d          -> showTer e <+> text "where" <+> showDecls d
  Var x              -> text x
  Con c es           -> text c <+> showTers es
  PCon c a es phi    -> text c <+> char '{' <+> showTer a <+> char '}' <+>
                         showTers es <+> showFormula phi
  Split f _ _ _      -> text f
  Sum _ n _          -> text n
  Undef _            -> text "undefined"
  IdP e0 e1 e2       -> text "IdP" <+> showTers [e0,e1,e2]
  Path i e           -> char '<' <> text (show i) <> char '>' <+> showTer e
  AppFormula e phi   -> showTer1 e <+> char '@' <+> showFormula phi
  Comp e0 e1 es      -> text "comp" <+> showTers [e0,e1]
                        <+> text (showSystem es)
  Trans e0 e1        -> text "transport" <+> showTers [e0,e1]
  Glue a ts          -> text "glue" <+> showTer1 a <+> text (showSystem ts)
  GlueElem a ts      -> text "glueElem" <+> showTer1 a <+> text (showSystem ts)
  CompElem a es t ts -> text "compElem" <+> showTer1 a <+> text (showSystem es)
                        <+> showTer1 t <+> text (showSystem ts)
  ElimComp a es t    -> text "elimComp" <+> showTer1 a <+> text (showSystem es)
                        <+> showTer1 t

showTers :: [Ter] -> Doc
showTers = hsep . map showTer1

showTer1 :: Ter -> Doc
showTer1 t = case t of
  U        -> char 'U'
  Con c [] -> text c
  Var x    -> text x
  Split{}  -> showTer t
  Sum{}    -> showTer t
  _        -> parens (showTer t)

showDecls :: [Decl] -> Doc
showDecls defs = hsep $ punctuate comma
                      [ text x <+> equals <+> showTer d | (x,(_,d)) <- defs ]

instance Show Val where
  show = render . showVal

showVal :: Val -> Doc
showVal v = case v of
  VU                -> char 'U'
  Ter t env         -> showTer t <+> showEnv env
  VCon c us         -> text c <+> showVals us
  VPCon c a us phi  -> text c <+> char '{' <+> showVal a <+> char '}' <+>
                       showVals us <+> showFormula phi
  VPi a b           -> text "Pi" <+> showVals [a,b]
  VPair u v         -> parens (showVal u <> comma <> showVal v)
  VSigma u v        -> text "Sigma" <+> showVals [u,v]
  VApp u v          -> showVal u <+> showVal1 v
  VSplit u v        -> showVal u <+> showVal1 v
  VVar x t          -> text x
  VFst u            -> showVal u <> text ".1"
  VSnd u            -> showVal u <> text ".2"
  VIdP v0 v1 v2     -> text "IdP" <+> showVals [v0,v1,v2]
  VPath i v         -> char '<' <> text (show i) <> char '>' <+> showVal v
  VAppFormula v phi -> showVal1 v <+> char '@' <+> showFormula phi
  VComp v0 v1 vs    -> text "comp" <+> showVals [v0,v1] <+> text (showSystem vs)
  VTrans v0 v1      -> text "trans" <+> showVals [v0,v1]
  VGlue a ts        -> text "glue" <+> showVal1 a <+> text (showSystem ts)
  VGlueElem a ts    -> text "glueElem" <+> showVal1 a <+> text (showSystem ts)
  VCompElem a es t ts -> text "compElem" <+> showVal1 a <+> text (showSystem es)
                         <+> showVal1 t <+> text (showSystem ts)
  VElimComp a es t    -> text "elimComp" <+> showVal1 a <+> text (showSystem es)
                         <+> showVal1 t

showVal1 :: Val -> Doc
showVal1 v = case v of
  VU        -> char 'U'
  VCon c [] -> text c
  VVar{}    -> showVal v
  Ter t@Sum{} _ -> showTer t
  _         -> parens (showVal v)

showVals :: [Val] -> Doc
showVals = hsep . map showVal1
