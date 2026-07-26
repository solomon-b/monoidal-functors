{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Exercises the generically derived rank-2 'Monoidal' for functor-interpreted
-- HKDs, at all three derivable instantiations:
--
-- * covariant product (@barbies@' @ApplicativeB@): 'combine' agrees with the
--   field-wise 'Pair'ing (@bprod@) and 'introduce' fills every field with
--   'Proxy' (@bpure Proxy@);
-- * coproduct: 'combine' injects a whole record all-'InL' or all-'InR';
-- * oplax product: 'combine' unzips a record of 'Pair's, and is inverse to the
--   covariant product 'combine'.
module Data.Functor.Rank2.MonoidalSpec (tests) where

--------------------------------------------------------------------------------

import Control.Category.LawsSupport (genInt)
import Data.Functor.Contravariant (Op (..), getOp)
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Rank2.Monoidal (Monoidal, Semigroupal (..), Unital (..), gcombineSum, gsplitProduct)
import Data.Functor.Sum (Sum (..))
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Void (Void, absurd)
import GHC.Generics (Generic, V1)
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

instance Semigroupal (->) Sum Either TestHKD where combine = gcombineSum

instance Unital (->) V1 Void TestHKD where introduce = absurd

instance Monoidal (->) Sum V1 Either Void TestHKD

instance Semigroupal Op Product (,) TestHKD where combine = Op gsplitProduct

instance Unital Op Proxy () TestHKD where introduce = Op (const ())

instance Monoidal Op Product Proxy (,) () TestHKD

deriving stock instance (Show (f Int), Show (f Bool), Show (f String)) => Show (TestHKD f)

deriving stock instance (Eq (f Int), Eq (f Bool), Eq (f String)) => Eq (TestHKD f)

-- | A nullary constructor. Exercises @U1@ and the unit path.
data EmptyHKD (f :: Type -> Type) = EmptyHKD
  deriving stock (Generic, Show, Eq)

instance Semigroupal (->) Product (,) EmptyHKD

instance Unital (->) Proxy () EmptyHKD

instance Monoidal (->) Product Proxy (,) () EmptyHKD

instance Semigroupal (->) Sum Either EmptyHKD where combine = gcombineSum

instance Unital (->) V1 Void EmptyHKD where introduce = absurd

instance Monoidal (->) Sum V1 Either Void EmptyHKD

--------------------------------------------------------------------------------
-- Monomorphic call sites (fix @cat@, @t1@, @t0@ for the derived instances).

combineHKD :: TestHKD f -> TestHKD g -> TestHKD (Product f g)
combineHKD x y = combine @(->) @Product @(,) (x, y)

introduceHKD :: TestHKD Proxy
introduceHKD = introduce @(->) @Proxy @() ()

combineSumHKD :: Either (TestHKD f) (TestHKD g) -> TestHKD (Sum f g)
combineSumHKD = combine @(->) @Sum @Either

splitHKD :: TestHKD (Product f g) -> (TestHKD f, TestHKD g)
splitHKD = getOp (combine @Op @Product @(,))

-- | The reference for the covariant product 'combine': field-wise 'Pair'.
refCombine :: TestHKD f -> TestHKD g -> TestHKD (Product f g)
refCombine (TestHKD a b c) (TestHKD a' b' c') =
  TestHKD (Pair a a') (Pair b b') (Pair c c')

-- | The reference for the coproduct 'combine': every field on one side.
refCombineSum :: Either (TestHKD f) (TestHKD g) -> TestHKD (Sum f g)
refCombineSum (Left (TestHKD a b c)) = TestHKD (InL a) (InL b) (InL c)
refCombineSum (Right (TestHKD a b c)) = TestHKD (InR a) (InR b) (InR c)

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

genProductHKD :: Gen (TestHKD (Product Maybe []))
genProductHKD = genHKD (\g -> Pair <$> Gen.maybe g <*> Gen.list (Range.linear 0 3) g)

--------------------------------------------------------------------------------
-- Covariant product properties

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

--------------------------------------------------------------------------------
-- Coproduct properties

-- | Injecting on the left sends every field to 'InL'.
coproductInjectsLeft :: Property
coproductInjectsLeft = property $ do
  x <- forAll genMaybeHKD
  let e = Left x :: Either (TestHKD Maybe) (TestHKD [])
  combineSumHKD e === refCombineSum e

-- | Injecting on the right sends every field to 'InR'.
coproductInjectsRight :: Property
coproductInjectsRight = property $ do
  y <- forAll genListHKD
  let e = Right y :: Either (TestHKD Maybe) (TestHKD [])
  combineSumHKD e === refCombineSum e

--------------------------------------------------------------------------------
-- Oplax product (split) properties

-- | Split then combine is the identity (product iso, one direction).
splitAfterCombine :: Property
splitAfterCombine = property $ do
  x <- forAll genMaybeHKD
  y <- forAll genListHKD
  splitHKD (combineHKD x y) === (x, y)

-- | Combine then split is the identity (product iso, other direction).
combineAfterSplit :: Property
combineAfterSplit = property $ do
  z <- forAll genProductHKD
  uncurry combineHKD (splitHKD z) === z

--------------------------------------------------------------------------------
-- Field-less record

-- | The field-less record is handled by the @U1@ path at every instantiation.
emptyRecord :: Property
emptyRecord = withTests 1 $ property $ do
  combine @(->) @Product @(,) (EmptyHKD :: EmptyHKD Maybe, EmptyHKD :: EmptyHKD []) === EmptyHKD
  introduce @(->) @Proxy @() () === (EmptyHKD :: EmptyHKD Proxy)
  combine @(->) @Sum @Either (Left EmptyHKD :: Either (EmptyHKD Maybe) (EmptyHKD [])) === EmptyHKD

--------------------------------------------------------------------------------

tests :: IO Bool
tests =
  checkSequential $
    Group
      "Data.Functor.Rank2.Monoidal"
      [ ("combine agrees with reference (Maybe/[])", combineAgreesWithRef),
        ("combine agrees with reference (Identity)", combineAgreesWithRefHomogeneous),
        ("introduce is all Proxy", introduceIsAllProxy),
        ("coproduct injects left", coproductInjectsLeft),
        ("coproduct injects right", coproductInjectsRight),
        ("split . combine = id", splitAfterCombine),
        ("combine . split = id", combineAfterSplit),
        ("empty record at every instantiation", emptyRecord)
      ]
