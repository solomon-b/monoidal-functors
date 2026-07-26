{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Exercises the generically derived rank-2 'Monoidal' for functor-interpreted
-- HKDs, at all three derivable instantiations:
--
-- * covariant product (@barbies@' @ApplicativeB@): 'combine' agrees with the
--   field-wise 'Pair'ing (@bprod@) and 'introduce' fills every field with
--   'Proxy' (@bpure Proxy@);
-- * coproduct: 'combine' injects a whole record all-'InL' or all-'InR';
-- * oplax product: 'combine' unzips a record of 'Pair's, and is inverse to the
--   covariant product 'combine'.
--
-- The covariant product also gets a laws pass (associativity, both unit laws,
-- and naturality), stated through @kindly-functors@' rank-2 'bmap' with
-- associators and unitors written inline. This doubles as an interop check that
-- 'combine' commutes with 'bmap'. The associators/unitors would collapse into
-- the shared "Data.Functor.Monoidal.Laws" machinery once the @Nat@-category
-- 'Control.Category.Tensor.Tensor' instances for 'Product' exist.
module Data.Functor.Rank2.MonoidalSpec (tests) where

--------------------------------------------------------------------------------

import Control.Category.LawsSupport (genInt)
import Data.Functor.Contravariant (Op (..), getOp)
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.Functor.Rank2.Monoidal (Monoidal, Semigroupal (..), Unital (..), gcombineSum, gcombineThese, gsplitProduct)
import Data.Functor.Sum (Sum (..))
import Data.Functor.These (These1 (..))
import Data.Kind (Type)
import Data.Maybe (listToMaybe, maybeToList)
import Data.Proxy (Proxy (..))
import Data.These (These (..))
import Data.Void (Void, absurd)
import GHC.Generics (Generic, V1)
import Hedgehog (Gen, Group (..), Property, checkSequential, forAll, property, withTests, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Kindly (CategoricalFunctor (..), Nat (..), bmap, type (~>))
import Prelude hiding (map)

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

instance Semigroupal (->) These1 These TestHKD where combine = gcombineThese

instance Monoidal (->) These1 V1 These Void TestHKD

instance Semigroupal Op Product (,) TestHKD where combine = Op gsplitProduct

instance Unital Op Proxy () TestHKD where introduce = Op (const ())

instance Monoidal Op Product Proxy (,) () TestHKD

-- | 'TestHKD' as a @kindly-functors@ rank-2 functor, so the law properties can
-- map interpretations through it with 'bmap'.
instance CategoricalFunctor TestHKD where
  type Dom TestHKD = (->) ~> (->)
  type Cod TestHKD = (->)
  map (Nat nt) (TestHKD a b c) = TestHKD (nt a) (nt b) (nt c)

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

instance Semigroupal (->) These1 These EmptyHKD where combine = gcombineThese

instance Monoidal (->) These1 V1 These Void EmptyHKD

--------------------------------------------------------------------------------
-- Monomorphic call sites (fix @cat@, @t1@, @t0@ for the derived instances).

combineHKD :: TestHKD f -> TestHKD g -> TestHKD (Product f g)
combineHKD x y = combine @(->) @Product @(,) (x, y)

introduceHKD :: TestHKD Proxy
introduceHKD = introduce @(->) @Proxy @() ()

combineSumHKD :: Either (TestHKD f) (TestHKD g) -> TestHKD (Sum f g)
combineSumHKD = combine @(->) @Sum @Either

combineTheseHKD :: These (TestHKD f) (TestHKD g) -> TestHKD (These1 f g)
combineTheseHKD = combine @(->) @These1 @These

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

-- | The reference for the These 'combine': every field follows the outer 'These'.
refCombineThese :: These (TestHKD f) (TestHKD g) -> TestHKD (These1 f g)
refCombineThese (This (TestHKD a b c)) = TestHKD (This1 a) (This1 b) (This1 c)
refCombineThese (That (TestHKD a b c)) = TestHKD (That1 a) (That1 b) (That1 c)
refCombineThese (These (TestHKD a b c) (TestHKD a' b' c')) =
  TestHKD (These1 a a') (These1 b b') (These1 c c')

--------------------------------------------------------------------------------
-- Associators and unitors for the 'Product' tensor on the functor category.
-- These stand in for the (as yet unwritten) @Nat@-category 'Tensor' instances.

-- | 'Product'\'s action on morphisms (the functor-category bifunctor).
prodNat ::
  (forall x. f x -> f' x) ->
  (forall x. g x -> g' x) ->
  Product f g a ->
  Product f' g' a
prodNat l r (Pair p q) = Pair (l p) (r q)

-- | The associator of 'Product' on the functor category.
assocProd :: Product f (Product g h) a -> Product (Product f g) h a
assocProd (Pair a (Pair b c)) = Pair (Pair a b) c

-- | The right unitor: 'Proxy' is the unit of 'Product'.
runitProd :: Product f Proxy a -> f a
runitProd (Pair a _) = a

-- | The left unitor.
lunitProd :: Product Proxy f a -> f a
lunitProd (Pair _ a) = a

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

-- | A 'These' generator that hits all three cases.
genTheseHKD :: Gen (These (TestHKD Maybe) (TestHKD []))
genTheseHKD =
  Gen.choice
    [ This <$> genMaybeHKD,
      That <$> genListHKD,
      These <$> genMaybeHKD <*> genListHKD
    ]

--------------------------------------------------------------------------------
-- Covariant product: agreement with the reference

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
-- Covariant product: monoidal laws (via kindly's rank-2 'bmap')

-- | Naturality: 'combine' commutes with maps into either tensor position.
-- Doubles as the interop check that 'combine' commutes with 'bmap'.
naturalityLaw :: Property
naturalityLaw = property $ do
  x <- forAll genMaybeHKD
  y <- forAll genListHKD
  bmap (prodNat maybeToList listToMaybe) (combineHKD x y)
    === combineHKD (bmap maybeToList x) (bmap listToMaybe y)

-- | Associativity: reassociating the domain 'Product' turns the right-nested
-- 'combine' into the left-nested one.
associativityLaw :: Property
associativityLaw = property $ do
  x <- forAll genMaybeHKD
  y <- forAll genListHKD
  z <- forAll genIdentityHKD
  bmap assocProd (combineHKD x (combineHKD y z))
    === combineHKD (combineHKD x y) z

-- | Right unit: combining with @'introduce' ()@ and projecting recovers the record.
rightUnitLaw :: Property
rightUnitLaw = property $ do
  x <- forAll genMaybeHKD
  bmap runitProd (combineHKD x introduceHKD) === x

-- | Left unit: the mirror of 'rightUnitLaw'.
leftUnitLaw :: Property
leftUnitLaw = property $ do
  x <- forAll genMaybeHKD
  bmap lunitProd (combineHKD introduceHKD x) === x

--------------------------------------------------------------------------------
-- Coproduct

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
-- These

-- | 'combine' at the 'These1' tensor follows the outer 'These' field-wise,
-- across all three cases.
theseAgreesWithRef :: Property
theseAgreesWithRef = property $ do
  e <- forAll genTheseHKD
  combineTheseHKD e === refCombineThese e

--------------------------------------------------------------------------------
-- Oplax product (split)

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
  combine @(->) @These1 @These (These EmptyHKD EmptyHKD :: These (EmptyHKD Maybe) (EmptyHKD [])) === EmptyHKD

--------------------------------------------------------------------------------

tests :: IO Bool
tests =
  checkSequential $
    Group
      "Data.Functor.Rank2.Monoidal"
      [ ("combine agrees with reference (Maybe/[])", combineAgreesWithRef),
        ("combine agrees with reference (Identity)", combineAgreesWithRefHomogeneous),
        ("introduce is all Proxy", introduceIsAllProxy),
        ("naturality (combine commutes with bmap)", naturalityLaw),
        ("associativity", associativityLaw),
        ("right unit", rightUnitLaw),
        ("left unit", leftUnitLaw),
        ("coproduct injects left", coproductInjectsLeft),
        ("coproduct injects right", coproductInjectsRight),
        ("these follows outer These", theseAgreesWithRef),
        ("split . combine = id", splitAfterCombine),
        ("combine . split = id", combineAfterSplit),
        ("empty record at every instantiation", emptyRecord)
      ]
