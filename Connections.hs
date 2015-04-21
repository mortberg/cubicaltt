{-# LANGUAGE TypeSynonymInstances, FlexibleInstances,
             GeneralizedNewtypeDeriving, TupleSections #-}
module Connections where

import Control.Applicative
import Data.List
import Data.Map (Map,(!),keys)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Test.QuickCheck

newtype Name = Name String
  deriving (Arbitrary,Eq,Ord)

instance Show Name where
  show (Name i) = i

swapName :: Name -> (Name,Name) -> Name
swapName k (i,j) | k == i    = j
                 | k == j    = i
                 | otherwise = k

-- | Directions
data Dir = Zero | One
  deriving (Eq,Ord)

instance Show Dir where
  show Zero = "0"
  show One  = "1"

instance Num Dir where
  Zero + Zero = Zero
  _    + _    = One

  Zero * _ = Zero
  One  * x = x

  abs      = id
  signum _ = One

  negate Zero = One
  negate One  = Zero

  fromInteger 0 = Zero
  fromInteger 1 = One
  fromInteger _ = error "fromInteger Dir"

instance Arbitrary Dir where
  arbitrary = do
    b <- arbitrary
    return $ if b then Zero else One

-- | Face

-- Faces of the form: [(i,0),(j,1),(k,0)]
type Face = Map Name Dir

instance Arbitrary Face where
  arbitrary = Map.fromList <$> arbitrary

showFace :: Face -> String
showFace alpha = concat [ "(" ++ show i ++ " = " ++ show d ++ ")"
                        | (i,d) <- Map.toList alpha ]

swapFace :: Face -> (Name,Name) -> Face
swapFace alpha ij = Map.mapKeys (`swapName` ij) alpha

-- Check if two faces are compatible
compatible :: Face -> Face -> Bool
compatible xs ys = and (Map.elems (Map.intersectionWith (==) xs ys))

compatibles :: [Face] -> Bool
compatibles []     = True
compatibles (x:xs) = all (x `compatible`) xs && compatibles xs

allCompatible :: [Face] -> [(Face,Face)]
allCompatible []     = []
allCompatible (f:fs) = map (f,) (filter (compatible f) fs) ++ allCompatible fs

-- Partial composition operation
meet :: Face -> Face -> Face
meet = Map.unionWith f
  where f d1 d2 = if d1 == d2 then d1 else error "meet: incompatible faces"

meetMaybe :: Face -> Face -> Maybe Face
meetMaybe x y = if compatible x y then Just $ meet x y else Nothing

meetCom :: Face -> Face -> Property
meetCom xs ys = compatible xs ys ==> xs `meet` ys == ys `meet` xs

meetAssoc :: Face -> Face -> Face -> Property
meetAssoc xs ys zs = compatibles [xs,ys,zs] ==>
                     xs `meet` (ys `meet` zs) == (xs `meet` ys) `meet` zs

meetId :: Face -> Bool
meetId xs = xs `meet` xs == xs

meets :: [Face] -> [Face] -> [Face]
meets xs ys = nub [ meet x y | x <- xs, y <- ys, compatible x y ]

meetss :: [[Face]] -> [Face]
meetss = foldr meets [eps]

leq :: Face -> Face -> Bool
alpha `leq` beta = meetMaybe alpha beta == Just alpha

comparable :: Face -> Face -> Bool
comparable alpha beta = alpha `leq` beta || beta `leq` alpha

incomparables :: [Face] -> Bool
incomparables []     = True
incomparables (x:xs) = all (not . (x `comparable`)) xs && incomparables xs

(~>) :: Name -> Dir -> Face
i ~> d = Map.singleton i d

eps :: Face
eps = Map.empty

minus :: Face -> Face -> Face
minus alpha beta = alpha Map.\\ beta

-- Compute the witness of A <= B, ie compute C s.t. B = CA
-- leqW :: Face -> Face -> Face
-- leqW = undefined

-- | Formulas
data Formula = Dir Dir
             | Atom Name
             | NegAtom Name
             | Formula :/\: Formula
             | Formula :\/: Formula
  deriving Eq

instance Show Formula where
  show (Dir Zero)  = "0"
  show (Dir One)   = "1"
  show (NegAtom a) = '-' : show a
  show (Atom a)    = show a
  show (a :\/: b)  = show1 a ++ " \\/ " ++ show1 b
    where show1 v@(a :/\: b) = "(" ++ show v ++ ")"
          show1 a = show a
  show (a :/\: b) = show1 a ++ " /\\ " ++ show1 b
    where show1 v@(a :\/: b) = "(" ++ show v ++ ")"
          show1 a = show a

arbFormula :: [Name] -> Int -> Gen Formula
arbFormula names s =
  frequency [ (1, Dir <$> arbitrary)
            , (1, Atom <$> elements names)
            , (1, NegAtom <$> elements names)
            , (s, do op <- elements [andFormula,orFormula]
                     op <$> arbFormula names s' <*> arbFormula names s')
            ]
  where s' = s `div` 3

instance Arbitrary Formula where
  arbitrary = do
      n <- arbitrary :: Gen Integer
      sized $ arbFormula (map (\x -> Name ('!' : show x))  [0..(abs n)])

class ToFormula a where
  toFormula :: a -> Formula

instance ToFormula Formula where
  toFormula = id

instance ToFormula Name where
  toFormula = Atom

instance ToFormula Dir where
  toFormula = Dir

negFormula :: Formula -> Formula
negFormula (Dir b)        = Dir (- b)
negFormula (Atom i)       = NegAtom i
negFormula (NegAtom i)    = Atom i
negFormula (phi :/\: psi) = orFormula (negFormula phi) (negFormula psi)
negFormula (phi :\/: psi) = andFormula (negFormula phi) (negFormula psi)

andFormula :: Formula -> Formula -> Formula
andFormula (Dir Zero) _  = Dir Zero
andFormula _ (Dir Zero)  = Dir Zero
andFormula (Dir One) phi = phi
andFormula phi (Dir One) = phi
andFormula phi psi       = phi :/\: psi

orFormula :: Formula -> Formula -> Formula
orFormula (Dir One) _    = Dir One
orFormula _ (Dir One)    = Dir One
orFormula (Dir Zero) phi = phi
orFormula phi (Dir Zero) = phi
orFormula phi psi        = phi :\/: psi

dnf :: Formula -> Set (Set (Name,Dir))
dnf (Dir One)      = Set.singleton Set.empty
dnf (Dir Zero)     = Set.empty
dnf (Atom n)       = Set.singleton (Set.singleton (n,1))
dnf (NegAtom n)    = Set.singleton (Set.singleton (n,0))
dnf (phi :\/: psi) = dnf phi `Set.union` dnf psi
dnf (phi :/\: psi) = Set.fromList [ a `Set.union` b
                                  | a <- Set.toList (dnf phi)
                                  , b <- Set.toList (dnf psi) ]

-- evalFormula :: Formula -> Face -> Formula
-- evalFormula phi alpha =
--   Map.foldWithKey (\i d psi -> act psi (i,Dir d)) phi alpha

  -- (Dir b) alpha  = Dir b
-- evalFormula (Atom i) alpha = case Map.lookup i alpha of
--                                Just b -> Dir b
--                                Nothing -> Atom i
-- evalFormula (Not phi) alpha = negFormula (evalFormula phi alpha)
-- evalFormula (phi :/\: psi) alpha =
--   andFormula (evalFormula phi alpha) (evalFormula psi alpha)
-- evalFormula (phi :\/: psi) alpha =
--   orFormula (evalFormula phi alpha) (evalFormula psi alpha)

-- find a better name?
-- phi b = max {alpha : Face | phi alpha = b}
invFormula :: Formula -> Dir -> [Face]
invFormula (Dir b') b          = [ eps | b == b' ]
invFormula (Atom i) b          = [ Map.singleton i b ]
invFormula (NegAtom i) b       = [ Map.singleton i (- b) ]
invFormula (phi :/\: psi) Zero = invFormula phi 0 `union` invFormula psi 0
invFormula (phi :/\: psi) One  = meets (invFormula phi 1) (invFormula psi 1)
invFormula (phi :\/: psi) b    = invFormula (negFormula phi :/\: negFormula psi) (- b)

propInvFormulaIncomp :: Formula -> Dir -> Bool
propInvFormulaIncomp phi b = incomparables (invFormula phi b)

-- prop_invFormula :: Formula -> Dir -> Bool
-- prop_invFormula phi b =
--   all (\alpha -> phi `evalFormula` alpha == Dir b) (invFormula phi b)

-- testInvFormula :: [Face]
-- testInvFormula = invFormula (Atom (Name 0) :/\: Atom (Name 1)) 1

-- | Nominal
-- gensym :: [Name] -> Name
-- gensym xs = head (ys \\ xs)
--   where ys = map Name $ ["i","j","k","l"] ++ map (('i':) . show) [0..]

-- gensymNice :: Name -> [Name] -> Name
-- gensymNice i@(Name s) xs = head (ys \\ xs)
--   where ys = i:map (\n -> Name (s ++ show n)) [0..]

gensym :: [Name] -> Name
gensym xs = Name ('!' : show max)
  where max = maximum' [ read x | Name ('!':x) <- xs ]
        maximum' [] = 0
        maximum' xs = maximum xs + 1

gensyms :: [Name] -> [Name]
gensyms d = let x = gensym d in x : gensyms (x : d)

class Nominal a where
  support :: a -> [Name]
  act     :: a -> (Name,Formula) -> a
  swap    :: a -> (Name,Name) -> a

fresh :: Nominal a => a -> Name
fresh = gensym . support

-- freshNice :: Nominal a => Name -> a -> Name
-- freshNice i = gensymNice i . support

freshs :: Nominal a => a -> [Name]
freshs = gensyms . support

unions :: Eq a => [[a]] -> [a]
unions = foldr union []

unionsMap :: Eq b => (a -> [b]) -> [a] -> [b]
unionsMap f = unions . map f

instance Nominal () where
  support () = []
  act () _   = ()
  swap () _  = ()

instance (Nominal a, Nominal b) => Nominal (a, b) where
  support (a, b) = support a `union` support b
  act (a,b) f    = (act a f,act b f)
  swap (a,b) n   = (swap a n,swap b n)

instance (Nominal a, Nominal b, Nominal c) => Nominal (a, b, c) where
  support (a,b,c) = unions [support a, support b, support c]
  act (a,b,c) f   = (act a f,act b f,act c f)
  swap (a,b,c) n  = (swap a n,swap b n,swap c n)

instance (Nominal a, Nominal b, Nominal c, Nominal d) =>
         Nominal (a, b, c, d) where
  support (a,b,c,d) = unions [support a, support b, support c, support d]
  act (a,b,c,d) f   = (act a f,act b f,act c f,act d f)
  swap (a,b,c,d) n  = (swap a n,swap b n,swap c n,swap d n)

instance (Nominal a, Nominal b, Nominal c, Nominal d, Nominal e) =>
         Nominal (a, b, c, d, e) where
  support (a,b,c,d,e)  =
    unions [support a, support b, support c, support d, support e]
  act (a,b,c,d,e) f    = (act a f,act b f,act c f,act d f, act e f)
  swap (a,b,c,d,e) n =
    (swap a n,swap b n,swap c n,swap d n,swap e n)

instance (Nominal a, Nominal b, Nominal c, Nominal d, Nominal e, Nominal h) =>
         Nominal (a, b, c, d, e, h) where
  support (a,b,c,d,e,h) =
    unions [support a, support b, support c, support d, support e, support h]
  act (a,b,c,d,e,h) f   = (act a f,act b f,act c f,act d f, act e f, act h f)
  swap (a,b,c,d,e,h) n  =
    (swap a n,swap b n,swap c n,swap d n,swap e n,swap h n)

instance Nominal a => Nominal [a]  where
  support xs  = unions (map support xs)
  act xs f    = [ act x f | x <- xs ]
  swap xs n   = [ swap x n | x <- xs ]

instance Nominal a => Nominal (Maybe a)  where
  support    = maybe [] support
  act v f    = fmap (`act` f) v
  swap a n   = fmap (`swap` n) a

instance Nominal Formula where
  support (Dir _)        = []
  support (Atom i)       = [i]
  support (NegAtom i)    = [i]
  support (phi :/\: psi) = support phi `union` support psi
  support (phi :\/: psi) = support phi `union` support psi

  act (Dir b) (i,phi)  = Dir b
  act (Atom j) (i,phi) | i == j    = phi
                       | otherwise = Atom j
  act (NegAtom j) (i,phi) | i == j    = negFormula phi
                          | otherwise = NegAtom j
  act (psi1 :/\: psi2) (i,phi) = act psi1 (i,phi) `andFormula` act psi2 (i,phi)
  act (psi1 :\/: psi2) (i,phi) = act psi1 (i,phi) `orFormula` act psi2 (i,phi)

  swap (Dir b) (i,j)  = Dir b
  swap (Atom k) (i,j)| k == i    = Atom j
                     | k == j    = Atom i
                     | otherwise = Atom k
  swap (NegAtom k) (i,j)| k == i    = NegAtom j
                        | k == j    = NegAtom i
                        | otherwise = NegAtom k
  swap (psi1 :/\: psi2) (i,j) = swap psi1 (i,j) :/\: swap psi2 (i,j)
  swap (psi1 :\/: psi2) (i,j) = swap psi1 (i,j) :\/: swap psi2 (i,j)

face :: Nominal a => a -> Face -> a
face = Map.foldWithKey (\i d a -> act a (i,Dir d))

-- the faces should be incomparable
type System a = Map Face a

showSystem :: Show a => System a -> String
showSystem ts =
  "[ " ++ concat (intersperse ", " [ showFace alpha ++ " -> " ++ show u
                                   | (alpha,u) <- Map.toList ts ]) ++ " ]"

insertSystem :: Face -> a -> System a -> System a
insertSystem alpha v ts = case find (comparable alpha) (Map.keys ts) of
  Just beta | alpha `leq` beta -> ts
            | otherwise        -> Map.insert alpha v (Map.delete beta ts)
  Nothing -> Map.insert alpha v ts

insertsSystem :: [(Face, a)] -> System a -> System a
insertsSystem faces us =
  foldr (\(alpha, ualpha) -> insertSystem alpha ualpha) us faces

mkSystem :: [(Face, a)] -> System a
mkSystem = flip insertsSystem Map.empty

unionSystem :: System a -> System a -> System a
unionSystem us vs = insertsSystem (Map.assocs us) vs


-- TODO: add some checks
transposeSystemAndList :: System [a] -> [b] -> [(System a,b)]
transposeSystemAndList _  []      = []
transposeSystemAndList tss (u:us) =
  (Map.map head tss,u):transposeSystemAndList (Map.map tail tss) us

-- Quickcheck this:
-- (i = phi) * beta = (beta - i) * (i = phi beta)

-- Now we ensure that the keys are incomparable
instance Nominal a => Nominal (System a) where
  support s = unions (map Map.keys $ Map.keys s)
              `union` support (Map.elems s)

  act s (i, phi) = addAssocs (Map.assocs s)
    where
    addAssocs [] = Map.empty
    addAssocs ((alpha,u):alphaus) =
      let s' = addAssocs alphaus
      in case Map.lookup i alpha of
        Just d -> let beta = Map.delete i alpha
                  in foldr (\delta s'' -> insertSystem (meet delta beta)
                                            (face u (Map.delete i delta)) s'')
                                            s' (invFormula (face phi beta) d)
        Nothing -> insertSystem alpha (act u (i,face phi alpha)) s'

  swap s ij = Map.mapKeys (`swapFace` ij) (Map.map (`swap` ij) s)

-- carve a using the same shape as the system b
border :: Nominal a => a -> System b -> System a
border v = Map.mapWithKey (const . face v)

shape :: System a -> System ()
shape = border ()

instance (Nominal a, Arbitrary a) => Arbitrary (System a) where
  arbitrary = do
    a <- arbitrary
    border a <$> arbitraryShape (support a)
    where
      arbitraryShape :: [Name] -> Gen (System ())
      arbitraryShape supp = do
        phi <- sized $ arbFormula supp
        return $ Map.fromList [(face,()) | face <- invFormula phi 0]

sym :: Nominal a => a -> Name -> a
sym a i = a `act` (i, NegAtom i)

rename :: Nominal a => a -> (Name, Name) -> a
rename a (i, j) = a `act` (i, Atom j)

conj, disj :: Nominal a => a -> (Name, Name) -> a
conj a (i, j) = a `act` (i, Atom i :/\: Atom j)
disj a (i, j) = a `act` (i, Atom i :\/: Atom j)

leqSystem :: Face -> System a -> Bool
alpha `leqSystem` us =
  not $ Map.null $ Map.filterWithKey (\beta _ -> alpha `leq` beta) us

-- assumes alpha <= shape us
proj :: (Nominal a, Show a) => System a -> Face -> a
proj us alpha | eps `Map.member` usalpha = usalpha ! eps
              | otherwise                =
  error $ "proj: eps not in " ++ show usalpha ++ "\nwhich  is the "
    ++ show alpha ++ "\nface of " ++ show us
  where usalpha = us `face` alpha

domain :: System a -> [Name]
domain  = keys . Map.unions . keys
