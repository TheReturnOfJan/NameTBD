{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Prelude hiding (Monoid)
import Test.QuickCheck
import Data.List
import qualified Data.Map.Strict as Map




------------------------------------Abstract algebra ------------------------

class Monoid a where
  add :: a -> a -> a
  addId :: a

class Monoid a => Group a where
  addInv :: a -> a
  
-- Actually it has to be an ABELIAN group
class Group a => Ring a where
  mul :: a -> a -> a
  mulId :: a

-- Actually has to be commutative ring
class Ring a => Field a where
  mulInv :: a -> a

sub :: Group a => a -> a -> a
sub p1 p2 = add p1 (addInv p2)

monoidIsAssociative :: (Monoid m, Eq m) => m -> m -> m -> Bool
monoidIsAssociative a b c = add a (add b c) == add (add a b) c

monoidHasIdentity :: (Monoid m, Eq m) => m -> Bool
monoidHasIdentity a = (add a addId) == a && (add addId a) == a

monoidIsCommutative :: (Monoid m, Eq m) => m -> m -> Bool
monoidIsCommutative a b = (add a b) == (add b a)

isMonoid :: forall m. (Monoid m, Eq m, Arbitrary m, Show m) => IO ()
isMonoid = do
  quickCheck $ monoidIsAssociative @m
  quickCheck $ monoidHasIdentity @m

groupHasInverse :: (Group g, Eq g) => g -> Bool
groupHasInverse a = add a (addInv a) == addId && add (addInv a) a == addId

isGroup :: forall g. (Group g, Eq g, Arbitrary g, Show g) => IO ()
isGroup = do
  isMonoid @g
  quickCheck $ groupHasInverse @g

isAbelianGroup :: forall g. (Group g, Eq g, Arbitrary g, Show g) => IO ()
isAbelianGroup = do
  isGroup @g
  quickCheck $ monoidIsCommutative @g

ringIsAssociative :: (Ring r, Eq r) => r -> r -> r -> Bool
ringIsAssociative a b c = mul a (mul b c) == mul (mul a b) c

ringHasIdentity :: (Ring r, Eq r) => r -> Bool
ringHasIdentity a = (mul a mulId) == a && (mul mulId a) == a

ringIsLeftDistributive :: (Ring r, Eq r) => r -> r -> r -> Bool
ringIsLeftDistributive a b c = mul a (add b c) == add (mul a b) (mul a c)

ringIsRightDistributive :: (Ring r, Eq r) => r -> r -> r -> Bool
ringIsRightDistributive a b c = mul (add b c) a == add (mul b a) (mul c a)

isRing :: forall r. (Ring r, Eq r, Arbitrary r, Show r) => IO ()
isRing = do
  isAbelianGroup @r
  quickCheck $ ringIsAssociative @r
  quickCheck $ ringHasIdentity @r
  quickCheck $ ringIsLeftDistributive @r
  quickCheck $ ringIsRightDistributive @r

ringIsCommutative :: (Ring r, Eq r) => r -> r -> Bool
ringIsCommutative a b = mul a b == mul b a

isCommutativeRing :: forall r. (Ring r, Eq r, Arbitrary r, Show r) => IO ()
isCommutativeRing = do
  isRing @r
  quickCheck $ ringIsCommutative @r

fieldHasInverse :: (Field f, Eq f) => f -> Bool
fieldHasInverse a
  | a == addId = True
  | otherwise  = mul a (mulInv a) == mulId && mul (mulInv a) a == mulId

isField :: forall f. (Field f, Eq f, Arbitrary f, Show f) => IO ()
isField = do
  isCommutativeRing @f
  quickCheck $ fieldHasInverse @f

---------------------------------- Integer insatnces ---------------------

instance Monoid Integer where
  add = (+)
  addId = 0

instance Group Integer where
  addInv a = -a

instance Ring Integer where
  mul = (*)
  mulId = 1

----------------------------------- Polynomials --------------------------

data Poly a = Poly (Map.Map Integer a)
  deriving (Show)

degree :: Poly a -> Integer
degree (Poly m)
  | Map.null m = 0
  | otherwise  = maximum . Map.keys $ m

coeff :: Ring a => Poly a -> Integer -> a
coeff (Poly m) k = Map.findWithDefault addId k m

instance (Eq a, Ring a) => Eq (Poly a) where
  p1 == p2 = all (\(a, b) -> a == b) [(a,b) |  let maxDegree = max (degree p1) (degree p2),
                                                   i <- [0 .. maxDegree],
                                                   let a = coeff p1 i,
                                                   let b = coeff p2 i]

instance Arbitrary a => Arbitrary (Poly a) where
  arbitrary = do
    list <- listOf (suchThat arbitrary (\(i, _) -> i >= 0))
    let map    = Map.fromList list
    return (Poly map)

instance Ring a => Monoid (Poly a) where
  add p1 p2 = Poly coeffs
    where maxDegree = max (degree p1) (degree p2)
          coeffs    = Map.fromList [(i, j) | i <- [0 .. maxDegree],
                                    let j = add (coeff p1 i) (coeff p2 i)]
  addId = Poly Map.empty

instance Ring a => Group (Poly a) where
  addInv (Poly m) = Poly (Map.map (\e -> addInv e) m)

mulCoeff :: Ring a => Poly a -> Poly a -> Integer -> a
mulCoeff p1 p2 i = foldl (\acc -> \ele -> add acc ele) addId $ (\(a, b) -> mul a b) <$> getList p1 p2 i
  where getList p1 p2 i = (\(a,b) -> (coeff p1 a, coeff p2 b)) <$> [(a, i - a) | a <- [0 .. i]]

instance Ring a => Ring (Poly a) where
  mul p1 p2 = Poly coeffs
    where maxDegree = (degree p1) + (degree p2)
          coeffs    = Map.fromList [(i, j) | i <- [0 .. maxDegree],
                                    let j = mulCoeff p1 p2 i]
  mulId     = Poly (Map.fromList [(0, mulId)])

expo :: Ring a => a -> Integer -> a
expo x 0 = mulId
expo x n = mul x (expo x (n-1))

eval :: Ring a => Poly a -> a -> a
eval p x = foldl (\acc -> \ele -> add acc ele) addId $ [i | let deg = degree p,
                                                            let ls = [0 .. deg],
                                                            let ls' = (\pow -> mul (coeff p pow) (expo x pow)) <$> ls,
                                                            i <- ls']

evalDistributesOverMul :: forall r. (Eq r, Ring r) => r -> Poly r -> Poly r -> Bool
evalDistributesOverMul r p1 p2 = mul (eval p1 r) (eval p2 r) == eval (mul p1 p2) r 


------------------------------------ Modular Arithmetic -------------------------

newtype ModInt = ModInt Integer
  deriving (Show, Eq)

instance Arbitrary ModInt where
  arbitrary = do
    i <- arbitrary
    return (modInt i)

ourPrime = 7

modInt :: Integer -> ModInt
modInt i = ModInt (i `mod` ourPrime)

instance Monoid ModInt where
  add (ModInt n1) (ModInt n2) = ModInt ((n1 + n2) `mod` ourPrime)
  addId = ModInt 0

instance Group ModInt where
  addInv (ModInt i) = ModInt (-i)

instance Ring ModInt where
  mul (ModInt n1) (ModInt n2) = ModInt ((n1 * n2) `mod` ourPrime)
  mulId = ModInt (1)


extendedEuclid :: Integer -> Integer -> (Integer, Integer)
extendedEuclid a b = extendedEuclid' a b 0 1 b 1 0 a
  where
    extendedEuclid' a b s t 0 olds oldt oldr = if oldr < 0 then (-olds, -oldt) else (olds, oldt)
    extendedEuclid' a b s t r olds oldt oldr = extendedEuclid' a' b' s' t' r' olds' oldt' oldr'
      where
        a' = a
        b' = b
        q = oldr `div` r
        oldr' = r
        olds' = s
        oldt' = t
        r' = oldr - q * r
        s' = olds - q * s
        t' = oldt - q * t
      
instance Field ModInt where
  mulInv (ModInt i) = ModInt (x)
    where
      x = fst $ extendedEuclid i ourPrime

raise :: ModInt -> Integer -> ModInt
raise b p
  | p < 0     = raise (mulInv b) (-p)
  | p == 0    = mulId
  | otherwise = mul b $ raise b (p - 1)

testRaise :: ModInt -> Integer -> Bool
testRaise b p = if (b /= addId) then mul (raise b p) (raise b (-p)) == mulId else True

---------------------- "Homomorphic Encryption" -----------------------------------

ourG = 5

newtype EncModInt = EncModInt ModInt
  deriving (Show, Eq)

encModInt :: Integer -> EncModInt
encModInt i = EncModInt $ raise (modInt ourG) i

instance Arbitrary EncModInt where
  arbitrary = do
    i <- suchThat arbitrary (>0)
    return (encModInt i)

instance Monoid EncModInt where
  add (EncModInt n1) (EncModInt n2) = EncModInt (mul n1 n2)
  addId = EncModInt $ mulId

instance Group EncModInt where
  addInv (EncModInt n) = EncModInt (mulInv n)

encMul :: EncModInt -> Integer -> EncModInt
encMul (EncModInt b) p = EncModInt $ raise b p

testEncAdd :: Integer -> Integer -> Bool
testEncAdd i1 i2 = encModInt (i1 + i2) == add (encModInt i1) (encModInt i2)

testEncMul :: Integer -> Integer -> Bool
testEncMul i1 i2 = encMul (encModInt i1) i2 == encModInt (i1 * i2)


-------------------------- Main -------------------------------------------

main :: IO ()
main = do
  isCommutativeRing @Integer
  isCommutativeRing @(Poly Integer)
  isCommutativeRing @(Poly ModInt)
  isField @ModInt
  quickCheck $ evalDistributesOverMul @Integer  
  quickCheck $ testRaise
  quickCheck $ testEncAdd
  quickCheck $ testEncMul

