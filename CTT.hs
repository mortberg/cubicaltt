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
type Label  = String

-- Branch of the form: c x1 .. xn -> e
type Branch = (Label,([Ident],Ter))

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Ident,Ter)]

-- Labelled sum: c (x1 : A1) .. (xn : An)
type LblSum = [(Ident,Tele)]

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
         | Con Label [Ter]
           -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Loc Ter [Branch]
           -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Loc Ident LblSum
           -- undefined
         | Undef Loc

           -- Id type
         | IdP Ter Ter Ter
         | Path Name Ter
         | AppFormula Ter Formula
           -- Kan Composition
         | Comp Ter Ter (System Ter)
         | Trans Ter Ter
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
         | VCon Label [Val]

           -- Id values
         | VIdP Val Val Val
         | VPath Name Val
         | VComp Val Val (System Val)
         | VTrans Val Val

           -- Glue values
         | VGlue Val (System Val)
         | VGlueElem Val (System Val)

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
  VVar _ _        -> True
  VFst v          -> isNeutral v
  VSnd v          -> isNeutral v
  VSplit _ v      -> isNeutral v
  VApp v _        -> isNeutral v
  VAppFormula v _ -> isNeutral v
  VComp a u ts    -> isNeutralComp a u ts
  VTrans a u      -> isNeutralTrans a u -- isNeutral a || isNeutralComp (a @@ 0) u Map.empty
  _               -> False

isNeutralSystem :: System Val -> Bool
isNeutralSystem = any isNeutral . Map.elems

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
-- unCon (KanUElem _ u) = unCon u
unCon v           = error $ "unCon: not a constructor: " ++ show v

--------------------------------------------------------------------------------
-- | Environments

data Env = Empty
         | Upd Env (Ident,Val)
         | Def [Decl] Env
         | Sub Env (Name,Formula)
  deriving Eq

upds :: Env -> [(Ident,Val)] -> Env
upds = foldl Upd

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
  U                -> char 'U'
  App e0 e1        -> showTer e0 <+> showTer1 e1
  Pi e0            -> text "Pi" <+> showTer e0
  Lam x t e        -> char '\\' <> text x <+> text "->" <+> showTer e
  Fst e            -> showTer e <> text ".1"
  Snd e            -> showTer e <> text ".2"
  Sigma e0         -> text "Sigma" <+> showTer e0
  Pair e0 e1       -> parens (showTer1 e0 <> comma <> showTer1 e1)
  Where e d        -> showTer e <+> text "where" <+> showDecls d
  Var x            -> text x
  Con c es         -> text c <+> showTers es
  Split l _ _      -> text "split" <+> showLoc l
  Sum _ n _        -> text "sum" <+> text n
  Undef _          -> text "undefined"
  IdP e0 e1 e2     -> text "IdP" <+> showTers [e0,e1,e2]
  Path i e         -> char '<' <> text (show i) <> char '>' <+> showTer e
  AppFormula e phi -> showTer1 e <+> char '@' <+> showFormula phi
  Comp e0 e1 es    -> text "comp" <+> showTers [e0,e1] <+> text (showSystem es)
  Trans e0 e1      -> text "transport" <+> showTers [e0,e1]
  Glue a ts        -> text "glue" <+> showTer a <+> text (showSystem ts)
  GlueElem a ts    -> text "glueElem" <+> showTer a <+> text (showSystem ts)

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

showVal, showVal1 :: Val -> Doc
showVal v = case v of
  VU                -> char 'U'
  Ter t env         -> showTer t <+> showEnv env
  VCon c us         -> text c <+> showVals us
  VPi a b           -> text "Pi" <+> showVals [a,b]
  VPair u v         -> parens (showVal1 u <> comma <> showVal1 v)
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
  VGlue a ts        -> text "glue" <+> showVal a <+> text (showSystem ts)
  VGlueElem a ts    -> text "glueElem" <+> showVal a <+> text (showSystem ts)
showVal1 v = case v of
  VU        -> char 'U'
  VCon c [] -> text c
  VVar{}    -> showVal v
  _         -> parens (showVal v)

showVals :: [Val] -> Doc
showVals = hsep . map showVal1
