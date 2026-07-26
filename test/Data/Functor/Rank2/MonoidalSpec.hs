{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Exercises the generically derived rank-2 'Monoidal' for functor-interpreted
-- HKDs. At the covariant @'Product' \/ 'Proxy'@ instantiation this is @barbies@'
-- @ApplicativeB@: 'combine' must agree with the hand-written field-wise
-- 'Pair'ing (@bprod@), 'introduce' must fill every field with 'Proxy' (@bpure
-- Proxy@), the two product projections must recover the operands, and the
-- field-less record must be handled by the 'U1' \/ 'introduce' path.
module Data.Functor.Rank2.MonoidalSpec (tests) where

--------------------------------------------------------------------------------

import Control.Category.LawsSupport (genInt)
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Rank2.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import GHC.Generics (Generic)
import Hedgehog (Gen, Group (..), Property, checkSequential, forAll, property, withTests, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude

--------------------------------------------------------------------------------
-- Test types

-- | A three-field record. Exercises @K1@, @M1@, and nested @:*:@.
data TestHKD f = TestHKD
  { thInt :: f Int,
    thBool :: f Bool,
    thString :: f String
  }
  deriving stock (Generic)

instance Semigroupal (->) Product (,) TestHKD

instance Unital (->) Proxy () TestHKD

instance Monoidal (->) Product Proxy (,) () TestHKD

deriving stock instance (Show (f Int), Show (f Bool), Show (f String)) => Show (TestHKD f)

deriving stock instance (Eq (f Int), Eq (f Bool), Eq (f String)) => Eq (TestHKD f)

-- | A nullary constructor. Exercises @U1@ and the 'introduce' path.
data EmptyHKD (f :: Type -> Type) = EmptyHKD
  deriving stock (Generic, Show, Eq)

instance Semigroupal (->) Product (,) EmptyHKD

instance Unital (->) Proxy () EmptyHKD

instance Monoidal (->) Product Proxy (,) () EmptyHKD

--------------------------------------------------------------------------------
-- Monomorphic call sites (fix @cat@, @t1@, @t0@ for the derived instance).

combineHKD :: TestHKD f -> TestHKD g -> TestHKD (Product f g)
combineHKD x y = combine @(->) @Product @(,) (x, y)

introduceHKD :: TestHKD Proxy
introduceHKD = introduce @(->) @Proxy @() ()

-- | The reference: 'combine' is the field-wise 'Pair'.
refCombine :: TestHKD f -> TestHKD g -> TestHKD (Product f g)
refCombine (TestHKD a b c) (TestHKD a' b' c') =
  TestHKD (Pair a a') (Pair b b') (Pair c c')

-- | Left projection of a paired record.
projL :: TestHKD (Product f g) -> TestHKD f
projL (TestHKD (Pair a _) (Pair b _) (Pair c _)) = TestHKD a b c

-- | Right projection of a paired record.
projR :: TestHKD (Product f g) -> TestHKD g
projR (TestHKD (Pair _ a) (Pair _ b) (Pair _ c)) = TestHKD a b c

--------------------------------------------------------------------------------
-- Generators

genString :: Gen String
genString = Gen.string (Range.linear 0 5) Gen.alpha

-- | Build a 'TestHKD' generator from a per-field wrapper.
genHKD :: (forall a. Gen a -> Gen (f a)) -> Gen (TestHKD f)
genHKD f = TestHKD <$> f genInt <*> f Gen.bool <*> f genString

genMaybeHKD :: Gen (TestHKD Maybe)
genMaybeHKD = genHKD Gen.maybe

genListHKD :: Gen (TestHKD [])
genListHKD = genHKD (Gen.list (Range.linear 0 3))

genIdentityHKD :: Gen (TestHKD Identity)
genIdentityHKD = genHKD (fmap Identity)

--------------------------------------------------------------------------------
-- Properties

-- | 'combine' agrees with the hand-written field-wise 'Pair' (@bprod@).
combineAgreesWithRef :: Property
combineAgreesWithRef = property $ do
  x <- forAll genMaybeHKD
  y <- forAll genListHKD
  combineHKD x y === refCombine x y

-- | 'combine' at a homogeneous interpretation also agrees with the reference.
combineAgreesWithRefHomogeneous :: Property
combineAgreesWithRefHomogeneous = property $ do
  x <- forAll genIdentityHKD
  y <- forAll genIdentityHKD
  combineHKD x y === refCombine x y

-- | 'introduce' fills every field with 'Proxy' (@bpure Proxy@).
introduceIsAllProxy :: Property
introduceIsAllProxy = withTests 1 $ property $ do
  introduceHKD === TestHKD Proxy Proxy Proxy

-- | The left projection of @combine x y@ recovers @x@ (product left unit).
leftProjectionRecovers :: Property
leftProjectionRecovers = property $ do
  x <- forAll genMaybeHKD
  y <- forAll genListHKD
  projL (combineHKD x y) === x

-- | The right projection of @combine x y@ recovers @y@ (product right unit).
rightProjectionRecovers :: Property
rightProjectionRecovers = property $ do
  x <- forAll genMaybeHKD
  y <- forAll genListHKD
  projR (combineHKD x y) === y

-- | The field-less record combines to itself and introduces to itself.
emptyRecord :: Property
emptyRecord = withTests 1 $ property $ do
  combine @(->) @Product @(,) (EmptyHKD :: EmptyHKD Maybe, EmptyHKD :: EmptyHKD []) === EmptyHKD
  introduce @(->) @Proxy @() () === (EmptyHKD :: EmptyHKD Proxy)

--------------------------------------------------------------------------------

tests :: IO Bool
tests =
  checkSequential $
    Group
      "Data.Functor.Rank2.Monoidal"
      [ ("combine agrees with reference (Maybe/[])", combineAgreesWithRef),
        ("combine agrees with reference (Identity)", combineAgreesWithRefHomogeneous),
        ("introduce is all Proxy", introduceIsAllProxy),
        ("left projection recovers x", leftProjectionRecovers),
        ("right projection recovers y", rightProjectionRecovers),
        ("empty record combine/introduce", emptyRecord)
      ]
