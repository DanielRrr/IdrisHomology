module Simplex

import Data.List

data Simplex a = MkS (List a)

data SimplicialComplex a = MkSC (List (Simplex a))

simplexEq : Eq a => Simplex a -> Simplex a -> Bool
simplexEq (MkS x) (MkS y) = x == y

implementation Eq a => Eq (Simplex a) where
  (==) = simplexEq

implementation Eq (Simplex a) => Ord (Simplex a) where
  compare (MkS x) (MkS y) = case compare (List.length x) (List.length y) of
    EQ => EQ
    LT => LT
    GT => GT

implementation Functor Simplex where
  map f (MkS xs) = MkS (map f xs)

implementation Functor SimplicialComplex where
  map f (MkSC xs) = MkSC (map (map f) xs)

implementation Applicative Simplex where
  pure x = MkS [x]
  (<*>) (MkS fs) (MkS xs) = MkS (fs <*> xs)

implementation Applicative SimplicialComplex where
  pure x = MkSC [MkS [x]]
  (<*>) (MkSC fs) (MkSC xs) = MkSC [ f <*> x | f <- fs, x <- xs]

implementation Monad Simplex where
  (>>=) (MkS xs) f = MkS (xs >>= f') where
    f' = toList' . f where
      toList' (MkS xs) = xs

fromList : Ord a => List (List a) -> SimplicialComplex a
fromList = MkSC . (sortBy compare) . (map MkS) . nub . map (sort . nub)

toList : SimplicialComplex a -> List (List a)
toList (MkSC xs) = map toList' xs where
  toList' (MkS xs) = xs

powerset : List a -> List (List a)
powerset [] = [[]]
powerset (x::xs) = map ((::) x) (powerset xs) ++ powerset xs

subset : Eq a => List a -> List a -> Bool
subset xs ys = and [ elem x ys | x <- ys ]

isSC : Eq a => SimplicialComplex a -> Bool
isSC m = and [ all (\x => x `elem` (toList m)) (powerset xs) | xs <- (toList m) ]

isSortedSC' : Ord a => SimplicialComplex a -> Bool
isSortedSC' m = sorted (toList m)

isSortedSC : Ord a => SimplicialComplex a -> Bool
isSortedSC m = isSC m && isSortedSC' m

nSimplexes : Nat -> SimplicialComplex a -> List (Simplex a)
nSimplexes n m = (map MkS) $ filter (\x => (List.length x) == n + 1) (toList m)
