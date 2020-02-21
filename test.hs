{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
-- have to set manually with :set -XTypeApplications
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Prelude hiding (Monoid)
import Test.QuickCheck

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

-- class Ring r => Poly p r | p -> r where
--   coeff :: p -> Int -> r
--   degree :: p -> Int

data Poly a = Poly [a]
  deriving Show

instance Monoid Int where
  add = (+)
  addId = 0

instance Group Int where
  inverse a = -a

instance Ring Int where
  mul = (*)
  mulId = 1

main :: IO ()
main = do
  isRing @Int

