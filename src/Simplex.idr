module Simplex

import Data.List

data Simplex a = MkS (List a)

simplexEq : Eq a => Simplex a -> Simplex a -> Bool
simplexEq (MkS x) (MkS y) = x == y

infixr 8 !!

data SimplicialComplex : a -> Type where
  SCNil : SimplicialComplex a
  (!!) : Simplex a -> SimplicialComplex a -> SimplicialComplex a

toListFun : SimplicialComplex a -> List (Simplex a)
toListFun SCNil = []
toListFun (x !! xs) = x :: toListFun xs

fromListFun : List (Simplex a) -> SimplicialComplex a
fromListFun [] = SCNil
fromListFun (x :: xs) = x !! fromListFun xs

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
  map f SCNil = SCNil
  map f (x !! xs) = (map f x) !! (map f xs)

implementation Applicative Simplex where
  pure x = MkS [x]
  (<*>) (MkS fs) (MkS xs) = MkS (fs <*> xs)

apSimplex : List (Simplex (a -> b)) -> List (Simplex a) -> List (Simplex b)
apSimplex fs xs = [ f <*> x | f <- fs, x <- xs ]

implementation Monad Simplex where
  (>>=) (MkS xs) f = MkS (xs >>= f') where
    f' = toList' . f where
      toList' (MkS xs) = xs

implementation Foldable Simplex where
  foldr f e (MkS []) = e
  foldr f e (MkS (x::xs)) = f x (foldr f e (MkS xs))

implementation Applicative SimplicialComplex where
  pure x = (MkS [x]) !! SCNil
  fs <*> xs = fromListFun (apSimplex (toListFun fs) (toListFun xs))

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

mkIsLte : Ord a => (x,y : a) -> Maybe (isLte x y)
mkIsLte x y =
    case (choose (x <= y)) of
        Left proofXLteY => Just proofXLteY
        Right proofNotXLteY => Nothing

data IsSortedSC : SimplicialComplex a -> Type where
  IsSortedEmpty : IsSortedSC SCNil
  IsSortedSingle : (x : Simplex a) -> IsSortedSC (x !! SCNil)
  IsSortedMany : (Ord a) => (x, y : Simplex a)
                                -> (xs : SimplicialComplex a)
                                  -> (isLte x y)
                                    -> IsSortedSC (y !! xs)
                                     -> IsSortedSC (x !! (y !! xs))
