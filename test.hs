{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
-- have to set manually with :set -XTypeApplications
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Prelude hiding (Monoid)
import Test.QuickCheck
import Data.List
import qualified Data.Map.Strict as Map

class Monoid a where
  add :: a -> a -> a
  addId :: a

class Monoid a => Group a where
  inverse :: a -> a

-- Actually it has to be an ABELIAN group
class Group a => Ring a where
  mul :: a -> a -> a
  mulId :: a

-- To get a field you need this exstra
-- commutative of mul
-- mul inverse

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
groupHasInverse a = add a (inverse a) == addId && add (inverse a) a == addId

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

instance Monoid Int where
  add = (+)
  addId = 0

instance Group Int where
  inverse a = -a

instance Ring Int where
  mul = (*)
  mulId = 1

data Poly a = Poly (Map.Map Int a)
  deriving (Show)

degree :: Poly a -> Int
degree (Poly m)
  | Map.null m = 0
  | otherwise  = maximum . Map.keys $ m

coeff :: Ring a => Poly a -> Int -> a
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
  inverse (Poly m) = Poly (Map.map (\e -> inverse e) m)

mulCoeff :: Ring a => Poly a -> Poly a -> Int -> a
mulCoeff p1 p2 i = foldl (\acc -> \ele -> add acc ele) addId $ (\(a, b) -> mul a b) <$> getList p1 p2 i
  where getList p1 p2 i = (\(a,b) -> (coeff p1 a, coeff p2 b)) <$> [(a, i - a) | a <- [0 .. i]]

instance Ring a => Ring (Poly a) where
  mul p1 p2 = Poly coeffs
    where maxDegree = (degree p1) + (degree p2)
          coeffs    = Map.fromList [(i, j) | i <- [0 .. maxDegree],
                                    let j = mulCoeff p1 p2 i]
  mulId     = Poly (Map.fromList [(0, mulId)])

examplePoly1 = Poly (Map.fromList [(2, 3), (1, -1), (0, 2)]) :: Poly Int
examplePoly2 = Poly (Map.fromList [(2, 2), (1, 5), (0, -10)]) :: Poly Int

expo :: Ring a => a -> Int -> a
expo x 0 = mulId
expo x n = mul x (expo x (n-1))

eval :: Ring a => Poly a -> a -> a
eval p x = foldl (\acc -> \ele -> add acc ele) addId $ [i | let deg = degree p,
                                                            let ls = [0 .. deg],
                                                            let ls' = (\pow -> mul (coeff p pow) (expo x pow)) <$> ls,
                                                            i <- ls']


-- (3x^2 - x + 2) * (2x^2 + 5x -10) =
-- 6x^4   -2x^3 + 4x^2
-- 15x^3  -5x^2 + 10x
-- -30x^2 +10x  - 20

-- (4,6), (3, 13), (2, -31), (1, 20), (0, -20)

-- fix :: (a -> a) -> a
-- fix f = x
--   where
--     x = f x

-- fibeeee = fix (\fib -> 0:1:(zipWith (+) fib (tail fib)))


main :: IO ()
main = do
  isCommutativeRing @Int
  isCommutativeRing @(Poly Int)


