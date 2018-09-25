{-# LANGUAGE TypeSynonymInstances, FlexibleInstances,
             GeneralizedNewtypeDeriving, TupleSections #-}
module Connections where

import Control.Applicative
import Data.List hiding (insert)
import Data.Set (Set,isProperSubsetOf)
import qualified Data.Set as Set
import Data.Maybe
-- import Test.QuickCheck
import Data.IORef
import System.IO.Unsafe

data Name = Name String | Gen {-# UNPACK #-} !Int
  deriving (Eq,Ord)

instance Show Name where
  show (Name i) = i
  show (Gen x)  = 'i' : show x

-- swap is only used for FRESH j!
swapName :: Name -> (Name,Name) -> Name
swapName k (i,j) | k == i    = j
--                 | k == j    = i
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

-- instance Arbitrary Dir where
--   arbitrary = do
--     b <- arbitrary
--     return $ if b then Zero else One

-- | Face

-- Faces of the form: [(i,0),(j,1),(k,0)]
-- Invariant: a name only occurs once in the face
type Face = [(Name,Dir)]

-- instance {-# OVERLAPPING #-} Arbitrary Face where
--   arbitrary = fromList <$> arbitrary

memberFace :: Name -> Face -> Bool
memberFace n [] = False
memberFace n ((i,_):xs) = n == i || memberFace n xs

notMemberFace :: Name -> Face -> Bool
notMemberFace n xs = not (memberFace n xs)

deleteFace :: Name -> Face -> Face
deleteFace i [] = []
deleteFace i ((j,x):xs) | i == j = xs
                        | otherwise = (j,x) : deleteFace i xs

showFace :: Face -> String
showFace alpha = concat [ "(" ++ show i ++ "=" ++ show d ++ ")" | (i,d) <- alpha ]

swapFace :: Face -> (Name,Name) -> Face
swapFace alpha ij = [ (swapName i ij,a) | (i,a) <- alpha ]

-- Check if two faces are compatible
compatible :: Face -> Face -> Bool
compatible [] ys = True
compatible ((i,a):xs) ys = case lookup i ys of
  Just d | d == a -> compatible xs ys
         | otherwise -> False
  Nothing -> compatible xs ys

compatibles :: [Face] -> Bool
compatibles []     = True
compatibles (x:xs) = all (x `compatible`) xs && compatibles xs

allCompatible :: [Face] -> [(Face,Face)]
allCompatible []     = []
allCompatible (f:fs) = map (f,) (filter (compatible f) fs) ++ allCompatible fs

insertFace :: (Name,Dir) -> Face -> Face
insertFace (i,d) xs = case lookup i xs of
  Just d' | d == d' -> xs
          | otherwise -> error "insertFace"
  Nothing -> (i,d) : xs

meetMaybe :: Face -> Face -> Maybe Face
meetMaybe [] ys = Just ys
meetMaybe ((i,d):xs) ys = case lookup i ys of
  Just d' | d == d' -> fmap (insertFace (i,d)) (meetMaybe xs ys)
          | otherwise -> Nothing
  Nothing -> fmap (insertFace (i,d)) (meetMaybe xs ys)

-- Partial composition operation
meetUnsafe :: Face -> Face -> Face
meetUnsafe xs ys = fromJust (meetMaybe xs ys)
  -- unionWith f
  -- where f d1 d2 = if d1 == d2 then d1 else error "meet: incompatible faces"


-- meetCom :: Face -> Face -> Property
-- meetCom xs ys = compatible xs ys ==> xs `meet` ys == ys `meet` xs

-- meetAssoc :: Face -> Face -> Face -> Property
-- meetAssoc xs ys zs = compatibles [xs,ys,zs] ==>
--                      xs `meet` (ys `meet` zs) == (xs `meet` ys) `meet` zs

-- meetId :: Face -> Bool
-- meetId xs = xs `meet` xs == xs

-- meets :: [Face] -> [Face] -> [Face]
-- meets xs ys = [ meet x y | x <- xs, y <- ys, compatible x y ]

meets :: [Face] -> [Face] -> [Face]
meets xs ys = [ f | Just f <- [ meetMaybe x y | x <- xs, y <- ys ]]

meetss :: [[Face]] -> [Face]
meetss = foldr meets [eps]

leq :: Face -> Face -> Bool
alpha `leq` beta = fmap sort (meetMaybe alpha beta) == Just (sort alpha)

comparable :: Face -> Face -> Bool
comparable alpha beta = alpha `leq` beta || beta `leq` alpha

incomparables :: [Face] -> Bool
incomparables []     = True
incomparables (x:xs) = all (not . (x `comparable`)) xs && incomparables xs

(~>) :: Name -> Dir -> Face
i ~> d = [(i,d)]

eps :: Face
eps = []

minus :: Face -> Face -> Face
minus alpha beta = alpha \\ beta

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

-- arbFormula :: [Name] -> Int -> Gen Formula
-- arbFormula names s =
--   frequency [ (1, Dir <$> arbitrary)
--             , (1, Atom <$> elements names)
--             , (1, NegAtom <$> elements names)
--             , (s, do op <- elements [andFormula,orFormula]
--                      op <$> arbFormula names s' <*> arbFormula names s')
--             ]
--   where s' = s `div` 3

-- instance Arbitrary Formula where
--   arbitrary = do
--       n <- arbitrary :: Gen Integer
--       sized $ arbFormula (map (\x -> Name ('!' : show x))  [0..(abs n)])

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
dnf (phi :\/: psi) = dnf phi `merge` dnf psi
dnf (phi :/\: psi) =
  foldr merge Set.empty [ Set.singleton (a `Set.union` b)
                        | a <- Set.toList (dnf phi)
                        , b <- Set.toList (dnf psi) ]

fromDNF :: Set (Set (Name,Dir)) -> Formula
fromDNF s = foldr (orFormula . foldr andFormula (Dir One)) (Dir Zero) fs
  where xss = map Set.toList $ Set.toList s
        fs = [ [ if d == Zero then NegAtom n else Atom n | (n,d) <- xs ] | xs <- xss ]

merge :: Set (Set (Name,Dir)) -> Set (Set (Name,Dir)) -> Set (Set (Name,Dir))
merge a b =
  let as = Set.toList a
      bs = Set.toList b
  in Set.fromList [ ai | ai <- as, not (any (`isProperSubsetOf` ai) bs) ] `Set.union`
     Set.fromList [ bi | bi <- bs, not (any (`isProperSubsetOf` bi) as) ]

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
invFormula (Atom i) b          = [ (i~>b) ]
invFormula (NegAtom i) b       = [ (i~>(- b)) ]
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

{-# NOINLINE freshVar #-}
freshVar :: IORef Int
freshVar = unsafePerformIO (newIORef 0)

-- succName (Name x) = Name ()

gensym :: [a] -> Name
gensym _ = unsafePerformIO $ do
  x <- readIORef freshVar
  modifyIORef freshVar succ
  return (Gen x)

-- gensym :: [Name] -> Name
-- gensym xs = Name ('!' : show max)
--   where max = maximum' [ read x | Name ('!':x) <- xs ]
--         maximum' [] = 0
--         maximum' xs = maximum xs + 1

gensyms :: [Name] -> [Name]
gensyms d = let x = gensym d in x : gensyms (x : d)

class Nominal a where
--  support :: a -> [Name]
  occurs :: Name -> a -> Bool
--  occurs x v = x `elem` support v
  act     :: Bool -> a -> (Name,Formula) -> a
  swap    :: a -> (Name,Name) -> a


fresh :: Nominal a => a -> Name
fresh _ = gensym [] -- . support

-- freshNice :: Nominal a => Name -> a -> Name
-- freshNice i = gensymNice i . support

freshs :: Nominal a => a -> [Name]
freshs _ = gensyms [] -- . support

-- unions :: [[a]] -> [a]
-- unions = concat -- foldr union []

-- unionsMap :: (a -> [b]) -> [a] -> [b]
-- unionsMap = concatMap -- unions . map f

newtype Nameless a = Nameless { unNameless :: a }
                   deriving (Eq, Ord)

instance Nominal (Nameless a) where
--  support _ = []
  occurs _ _ = False
  act _ x _   = x
  swap x _  = x

instance Nominal () where
--  support () = []
  occurs _ _ = False
  act _ () _   = ()
  swap () _  = ()

instance (Nominal a, Nominal b) => Nominal (a, b) where
--  support (a, b) = support a `union` support b
  occurs x (a,b) = occurs x a || occurs x b
  act x (a,b) f    = (act x a f,act x b f)
  swap (a,b) n   = (swap a n,swap b n)

instance (Nominal a, Nominal b, Nominal c) => Nominal (a, b, c) where
--  support (a,b,c) = unions [support a, support b, support c]
  occurs x (a,b,c) = or [occurs x a,occurs x b,occurs x c]
  act x (a,b,c) f   = (act x a f,act x b f,act x c f)
  swap (a,b,c) n  = (swap a n,swap b n,swap c n)

instance (Nominal a, Nominal b, Nominal c, Nominal d) =>
         Nominal (a, b, c, d) where
--  support (a,b,c,d) = unions [support a, support b, support c, support d]
  occurs x (a,b,c,d) = or [occurs x a,occurs x b,occurs x c,occurs x d]
  act x (a,b,c,d) f   = (act x a f,act x b f,act x c f,act x d f)
  swap (a,b,c,d) n  = (swap a n,swap b n,swap c n,swap d n)

instance (Nominal a, Nominal b, Nominal c, Nominal d, Nominal e) =>
         Nominal (a, b, c, d, e) where
  -- support (a,b,c,d,e)  =
  --   unions [support a, support b, support c, support d, support e]
  occurs x (a,b,c,d,e) =
    or [occurs x a,occurs x b,occurs x c,occurs x d,occurs x e]
  act x (a,b,c,d,e) f    = (act x a f,act x b f,act x c f,act x d f, act x e f)
  swap (a,b,c,d,e) n =
    (swap a n,swap b n,swap c n,swap d n,swap e n)

instance (Nominal a, Nominal b, Nominal c, Nominal d, Nominal e, Nominal h) =>
         Nominal (a, b, c, d, e, h) where
  -- support (a,b,c,d,e,h) =
  --   unions [support a, support b, support c, support d, support e, support h]
  occurs x (a,b,c,d,e,h) =
    or [occurs x a,occurs x b,occurs x c,occurs x d,occurs x e,occurs x h]
  act x (a,b,c,d,e,h) f   = (act x a f,act x b f,act x c f,act x d f, act x e f, act x h f)
  swap (a,b,c,d,e,h) n  =
    (swap a n,swap b n,swap c n,swap d n,swap e n,swap h n)

instance Nominal a => Nominal [a]  where
--  support xs  = unions (map support xs)
  occurs x xs = any (occurs x) xs
  act b xs f    = [ act b x f | x <- xs ]
  swap xs n   = [ swap x n | x <- xs ]

instance Nominal a => Nominal (Maybe a)  where
--  support    = maybe [] support
  occurs x   = maybe False (occurs x)
  act x v f    = fmap (\y -> act x y f) v
  swap a n   = fmap (`swap` n) a

instance Nominal Formula where
  -- support (Dir _)        = []
  -- support (Atom i)       = [i]
  -- support (NegAtom i)    = [i]
  -- support (phi :/\: psi) = support phi `union` support psi
  -- support (phi :\/: psi) = support phi `union` support psi

  occurs x u = case u of
    Dir _ -> False
    Atom i -> x == i
    NegAtom i -> x == i
    phi :/\: psi -> occurs x phi || occurs x psi
    phi :\/: psi -> occurs x phi || occurs x psi

  act x (Dir b) (i,phi)  = Dir b
  act x (Atom j) (i,phi) | i == j    = phi
                       | otherwise = Atom j
  act x (NegAtom j) (i,phi) | i == j    = negFormula phi
                          | otherwise = NegAtom j
  act x (psi1 :/\: psi2) (i,phi) = act x psi1 (i,phi) `andFormula` act x psi2 (i,phi)
  act x (psi1 :\/: psi2) (i,phi) = act x psi1 (i,phi) `orFormula` act x psi2 (i,phi)

  swap (Dir b) (i,j)  = Dir b
  swap (Atom k) (i,j)| k == i    = Atom j
                     | k == j    = Atom i
                     | otherwise = Atom k
  swap (NegAtom k) (i,j)| k == i    = NegAtom j
                        | k == j    = NegAtom i
                        | otherwise = NegAtom k
  swap (psi1 :/\: psi2) (i,j) = swap psi1 (i,j) :/\: swap psi2 (i,j)
  swap (psi1 :\/: psi2) (i,j) = swap psi1 (i,j) :\/: swap psi2 (i,j)

supportFormula :: Formula -> [Name]
supportFormula (Dir _)        = []
supportFormula (Atom i)       = [i]
supportFormula (NegAtom i)    = [i]
supportFormula (phi :/\: psi) = supportFormula phi `union` supportFormula psi
supportFormula (phi :\/: psi) = supportFormula phi `union` supportFormula psi

-- foldrWithKey (\i d a -> act x a (i,Dir d))
face :: Nominal a => a -> Face -> a
face x [] = x
face x ((i,d):xs) -- | not (i `occurs` x) = face x xs
                  | otherwise = face (act True x (i,Dir d)) xs

-- the faces should be incomparable
newtype System a = Sys [(Face,a)]
  deriving (Eq,Show)

unSys :: System a -> [(Face,a)]
unSys (Sys xs) = xs

keys :: System a -> [Face]
keys (Sys xs) = map fst xs

elems :: System a -> [a]
elems (Sys xs) = map snd xs

-- insert :: (Face,a) -> System a -> System a
-- insert x (Sys xs) = Sys (x:xs)

emptySystem :: System a
emptySystem = Sys []

nullSystem :: System a -> Bool
nullSystem (Sys []) = True
nullSystem _ = False

filterWithKey :: (Face -> a -> Bool) -> System a -> System a
filterWithKey f (Sys xs) = Sys $ filter (uncurry f) xs

mapSystem :: (a -> b) -> System a -> System b
mapSystem f (Sys xs) = Sys $ mapSystem' xs
  where
    mapSystem' [] = []
    mapSystem' ((a,x):xs) = (a,f x) : mapSystem' xs

mapKeys :: (Face -> Face) -> System a -> System a
mapKeys f (Sys xs) = mkSystem [ (f a,x) | (a,x) <- xs]

mapWithKey :: (Face -> a -> b) -> System a -> System b
mapWithKey f (Sys xs) = Sys [ (a,f a x) | (a,x) <- xs ]

intersectionWith :: (a -> b -> c) -> System a -> System b -> System c
intersectionWith _ (Sys []) _ = emptySystem
intersectionWith f (Sys ((a,x):xs)) (Sys ys) = case lookup a ys of
  Just y -> insertSystem a (f x y) (intersectionWith f (Sys xs) (Sys ys))
  Nothing -> intersectionWith f (Sys xs) (Sys ys)

intersectionWithKey :: (Face -> a -> b -> c) -> System a -> System b -> System c
intersectionWithKey _ (Sys []) _ = emptySystem
intersectionWithKey f (Sys ((a,x):xs)) (Sys ys) = case lookup a ys of
  Just y -> insertSystem a (f a x y) (intersectionWithKey f (Sys xs) (Sys ys))
  Nothing -> intersectionWithKey f (Sys xs) (Sys ys)

(!) :: System a -> Face -> a
(Sys xs) ! a = case lookup a xs of
  Just x -> x
  Nothing -> error "(!): face doesn't exist in system"

member :: Face -> System a -> Bool
member a (Sys xs) = or [ a == x | (x,_) <- xs ]

-- showSystem :: Show a => System a -> String
-- showSystem = showListSystem . toList

insertSystem :: Face -> a -> System a -> System a
insertSystem alpha v ts
  | any (leq alpha) (keys ts) = ts
  | otherwise = Sys $ (alpha,v) : unSys (filterWithKey (\gamma _ -> not (gamma `leq` alpha)) ts)

insertsSystem :: [(Face, a)] -> System a -> System a
insertsSystem faces us = foldr (uncurry insertSystem) us faces

mkSystem :: [(Face, a)] -> System a
mkSystem xs = insertsSystem xs emptySystem

unionSystem :: System a -> System a -> System a
unionSystem (Sys us) vs = insertsSystem us vs

-- joinSystem :: System (System a) -> System a
-- joinSystem (Sys tss) = mkSystem $
--   [ (alpha `meet` beta,t) | (alpha,Sys ts) <- tss, (beta,t) <- ts ]

-- Calculates shape corresponding to (phi=dir)
invSystem :: Formula -> Dir -> System ()
invSystem phi dir = mkSystem $ map (,()) $ invFormula phi dir

allSystem :: Name -> System a -> System a
allSystem i = filterWithKey (\alpha _ -> i `notMemberFace` alpha)

-- TODO: add some checks
transposeSystemAndList :: System [a] -> [b] -> [(System a,b)]
transposeSystemAndList _  []      = []
transposeSystemAndList tss (u:us) =
   (mapSystem head tss,u) : transposeSystemAndList (mapSystem tail tss) us

-- Quickcheck this:
-- (i = phi) * beta = (beta - i) * (i = phi beta)

-- Now we ensure that the keys are incomparable
instance Nominal a => Nominal (System a) where
  -- support s = unions (map keys $ keys s)
  --             `union` support (elems s)

  occurs x s = x `elem` (concatMap (map fst) $ keys s) || occurs x (elems s)

  act b (Sys s) (i, phi) = addAssocs s
    where
    addAssocs [] = emptySystem
    addAssocs ((alpha,u):alphaus) =
      let s' = addAssocs alphaus
      in case lookup i alpha of
        Just d -> let beta = deleteFace i alpha
                  in foldr (\delta s'' -> insertSystem (meetUnsafe delta beta)
                                            (face u (deleteFace i delta)) s'')
                                            s' (invFormula (face phi beta) d)
        Nothing -> insertSystem alpha (act b u (i,face phi alpha)) s'

  swap s ij = mapKeys (`swapFace` ij) (mapSystem (`swap` ij) s)

-- carve a using the same shape as the system b
border :: Nominal a => a -> System b -> System a
border v = mapWithKey (const . face v)

shape :: System a -> System ()
shape = border ()

-- instance {-# OVERLAPPING #-} (Nominal a, Arbitrary a) => Arbitrary (System a) where
--   arbitrary = do
--     a <- arbitrary
--     border a <$> arbitraryShape (support a)
--     where
--       arbitraryShape :: [Name] -> Gen (System ())
--       arbitraryShape supp = do
--         phi <- sized $ arbFormula supp
--         return $ fromList [(face,()) | face <- invFormula phi 0]

sym :: Nominal a => a -> Name -> a
sym a i = act False a (i, NegAtom i)

conj, disj :: Nominal a => a -> (Name, Name) -> a
conj a (i, j) = act False a (i, Atom i :/\: Atom j)
disj a (i, j) = act False a (i, Atom i :\/: Atom j)

leqSystem :: Face -> System a -> Bool
alpha `leqSystem` us =
  not $ nullSystem $ filterWithKey (\beta _ -> alpha `leq` beta) us

-- -- assumes alpha <= shape us
-- proj :: (Nominal a, Show a) => System a -> Face -> a
-- proj us alpha = us `face` alpha ! eps
--   --   | eps `member` usalpha = usalpha ! eps
--   --   | otherwise            =
--   -- error $ "proj: eps not in " ++ show usalpha ++ "\nwhich  is the "
--   --   ++ show alpha ++ "\nface of " ++ show us
--   -- where usalpha = us `face` alpha

domain :: System a -> [Name]
domain  = map fst . concat . keys

