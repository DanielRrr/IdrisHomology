module Modules

%access public export

interface (Semigroup a, Semigroup b, Monoid a, Monoid b) => Homo a b where
  homo : a -> b

interface Monoid a => Group a where
  inverse : a -> a

infixl 8 <**>

interface Group a => Ring a where
  (<**>) : a -> a -> a

interface Group a => AbelianGroup a where
  commutative : (x,y : a) -> (x <+> y) = (y <+> x)

interface (AbelianGroup a, Ring a) => IsRing a where
  FirtsDistr : (x, y, z : a) -> x <**> (y <+> z) = x <**> y <+> x <**> z
  SecondDisrt : (x, y, z : a) -> (x <+> y) <**> z = x <**> z <+> y <**> z

interface Ring a => RingWithOne a where
  e : a

interface (IsRing a, RingWithOne a) => IsRingWithOne a where
  UnitLaw1 : (x : a) -> x <**> ringMempty = x
  UnitLaw2 : (x : a) -> ringMempty <**> x = x

infixr 9 <..>

interface (RingWithOne b, AbelianGroup a) => LeftRModule a b where
  (<..>) : b -> a -> a

interface LeftRModule a b => IsLeftRModule a b where
  FirstLaw : (x,y : b) -> (z : a) -> (x <+> y) <..> z = (x <..> z) <+> (y <..> z)
  SecondLaw : (x : b) -> (y, z : a) -> x <..> (y <+> z) = (x <..> y) <+> (x <..> z)
  ThirdLaw : (x,y : b) -> (z : a) -> (x <**> y) <..> z = x <..> (y <..> z)
  FourthLaw : (x : b) -> (y : a) -> (e <**> x) <..> y = x <..> y
