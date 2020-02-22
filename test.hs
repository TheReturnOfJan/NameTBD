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

instance Monoid Int where
  add = (+)
  addId = 0

instance Group Int where
  inverse a = -a

instance Ring Int where
  mul = (*)
  mulId = 1

-- class Ring r => Poly p r | p -> r where
--   coeff :: p -> Int -> r
--   degree :: p -> Int

data Poly a = Poly [a]
  deriving (Show)

instance Arbitrary a => Arbitrary (Poly a) where
  arbitrary = do
    list <- arbitrary
    return (Poly list)

instance (Eq a, Monoid a) => Eq (Poly a) where
  p1 == p2 = (dropWhile (==addId) (getList p1)) == (dropWhile (==addId) (getList p2))

degree :: Poly a -> Int
degree (Poly list) = (length list) - 1

getList :: Poly a -> [a]
getList (Poly ls) = ls

stripZeros :: (Ring a, Eq a) => Poly a -> Poly a
stripZeros p = Poly (dropWhile (==addId) (getList p))

examplePoly1 :: Poly Int  = Poly [3, 2, -1, 7]
examplePoly2 :: Poly Int  = Poly [2, 2, 1, 3, 1, -3]
-- 3x^2 + 3  -    [3, 0, 3]
-- 3x^2 -3x + 2 - [3, -3, 2]
-- [1, 2, 4, 5, 6]
-- [0, 0 ,2, 3, 5]
-- [(4, 1), (0, -1)]
-- [(2, 2), (1, -2), (0, 4)]

indexed :: [a] -> [(Int, a)]
indexed a = indexed' (length a - 1) a
  where indexed' n (x:xs) = (n, x):(indexed' (n-1) xs)
        indexed' n []     = []

-- assume fist list is sorted by Int
unindexed :: Ring a => [(Int, a)] -> [a]
unindexed []                   = []
unindexed ((ix, x):[])         = x:(replicate ix addId)
unindexed ((ix, x):(iy, y):xs) = x:(padWithId (ix - iy) (unindexed ((iy,y):xs)))
  where padWithId 0 ls = ls
        padWithId 1 ls = ls
        padWithId n ls = padWithId (n-1) (addId:ls)

roundaboutIsIdentity :: [Int] -> Bool
roundaboutIsIdentity ls = ls == (unindexed $ (indexed ls))

compareTuple :: (Int, a) -> (Int, a) -> Ordering
compareTuple (a,_) (b,_)
  | a == b = EQ
  | a < b = LT
  | a > b = GT

roundaboutIsIdentity2 :: [(Int, Int)] -> Bool
roundaboutIsIdentity2 ls = l == (indexed $ (unindexed l))
  where l = sortBy compareTuple ls

padPoly :: Ring a => Int -> Poly a -> Poly a
padPoly n p
  | n == deg = p
  | n < deg  = p
  | n > deg  = padPoly n (pushZero p)
  where deg = degree p
        pushZero (Poly list) = Poly (addId:list)

instance Functor Poly where
  fmap f (Poly list) = Poly (fmap f list)

instance Ring a => Monoid (Poly a) where
  add p1 p2 = let maxDegree = max (degree p1) (degree p2)
                  p1' = padPoly maxDegree p1
                  p2' = padPoly maxDegree p2
                  l1  = getList p1'
                  l2  = getList p2' in
                Poly ((\(a, b) -> add a b) <$> zip l1 l2)          
  addId = Poly []

instance Ring a => Group (Poly a) where
  inverse p = let l = getList p in
                Poly ((\a -> inverse a) <$> l)

instance Ring a => Ring (Poly a) where
  mul p1 p2 = undefined
  mulId = undefined
                  

main :: IO ()
main = do
  isRing @Int
  isGroup @(Poly Int)
  quickCheck roundaboutIsIdentity
