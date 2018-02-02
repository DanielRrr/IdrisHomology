module Simplex

data Simplex a = MkSimplex (List a)

data SimplicialComplex a = MkSComplex (List (Simplex a))

simplexEq : Eq a => Simplex a -> Simplex a -> Bool
simplexEq (MkSimplex x) (MkSimplex y) = x == y

implementation Eq a => Eq (Simplex a) where
  (==) = simplexEq

implementation Eq (Simplex a) => Ord (Simplex a) where
  compare (MkSimplex x) (MkSimplex y) = case compare (List.length x) (List.length y) of
    EQ => EQ
    LT => LT
    GT => GT

implementation Functor Simplex where
  map f (MkSimplex xs) = MkSimplex (map f xs)

implementation Functor SimplicialComplex where
  map f (MkSComplex xs) = MkSComplex (map (map f) xs)

fromList : Ord a => List (List a) -> SimplicialComplex a
fromList = MkSComplex . (sortBy compare) . (map MkSimplex) . nub . map (sort . nub) 
