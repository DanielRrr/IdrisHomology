module Simplex

import Data.List

data Simplex a = MkS (List a)

data SimplicialComplex a = MkSC (List (Simplex a))

simplexEq : Eq a => Simplex a -> Simplex a -> Bool
simplexEq (MkS x) (MkS y) = x == y

infixr 8 !!

(!!) : Simplex a -> SimplicialComplex a -> SimplicialComplex a
(!!) x (MkSC xs) = MkSC (x :: xs)

infixr 8 !!!

infixr 8 !!!!

data SimplicialComplex' : a -> Type where
  SCNil : SimplicialComplex' a
  (!!!!) : Simplex a -> SimplicialComplex a -> SimplicialComplex a

(!!!) : SimplicialComplex a -> SimplicialComplex a -> SimplicialComplex a
(!!!) (MkSC xs) (MkSC []) = MkSC xs
(!!!) (MkSC xs) (MkSC (y::ys)) = MkSC (xs ++ [y] ++ ys)

implementation Eq a => Eq (Simplex a) where
  (==) = simplexEq

implementation Eq (Simplex a) => Ord (Simplex a) where
  compare (MkS x) (MkS y) = case compare (List.length x) (List.length y) of
    EQ => EQ
    LT => LT
    GT => GT

implementation Functor Simplex where
  map f (MkS xs) = MkS (map f xs)

implementation SimplicialComplex' where
  map f SCNil = SCNil
  map f (x !!!! xs) = (map f x) !!!! (map f xs)

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

data SCElem : Simplex a -> SimplicialComplex a -> Type where
  SCHere : SCElem x (x !! xs)
  SCThere : (m : SCElem x xs) -> SCElem x (y !! xs)

data Subset : SimplicialComplex a -> SimplicialComplex a -> Type where
  subset : (x : Simplex a) -> (xs, ys : SimplicialComplex a) -> (SCElem x xs -> SCElem x ys) -> Subset xs ys

data So : Bool -> Type where
  Oh : So True

isLte : Ord a => a -> a -> Type
isLte x y = So (x <= y)

choose : (b : Bool) -> Either (So b) (So (not b))
choose True  = Left Oh
choose False = Right Oh

mkIsLte : Ord e => (x:e) -> (y:e) -> Maybe (isLte x y)
mkIsLte x y =
    case (choose (x <= y)) of
        Left proofXLteY =>
            Just proofXLteY
        Right proofNotXLteY =>
            Nothing

fromListFun : List (Simplex a) -> SimplicialComplex a
fromListFun [] = MkSC []
fromListFun (x::xs) = x !! MkSC xs

data IsSortedSC : SimplicialComplex a -> Type where
  IsSortedEmpty : IsSortedSC (MkSC [])
  IsSortedSingle : (x : Simplex a) -> IsSortedSC (MkSC ([x]))
  IsSortedMany : (Ord a) => (x, y : Simplex a)
                                -> (xs : SimplicialComplex a)
                                  -> (isLte x y)
                                    -> IsSortedSC (y !! xs)
                                     -> IsSortedSC (x !! (y !! xs))

mkSorted : Ord a => (xs : SimplicialComplex a) -> Maybe (IsSortedSC xs)
mkSorted (MkSC []) = Just IsSortedEmpty
mkSorted (MkSC [x]) = Just (IsSortedSingle x)

fromList : Ord a => List (List a) -> SimplicialComplex a
fromList = MkSC . (sortBy compare) . (map MkS) . nub . map (sort . nub)

toList : SimplicialComplex a -> List (List a)
toList (MkSC xs) = map toList' xs where
  toList' (MkS xs) = xs

nSimplexes : Nat -> SimplicialComplex a -> List (Simplex a)
nSimplexes n m = (map MkS) $ filter (\x => (List.length x) == n + 1) (toList m)
