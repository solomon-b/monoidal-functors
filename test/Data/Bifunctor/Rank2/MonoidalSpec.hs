{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Exercises the generically derived rank-2 'Monoidal' for bifunctor-interpreted
-- HKDs, at all three derivable instantiations:
--
-- * covariant product: 'combine' agrees with the field-wise 'Pair'ing and
--   'introduce' fills every field with the unit bifunctor @'Joker' 'Proxy'@;
-- * coproduct: 'combine' injects a whole record all-'L2' or all-'R2';
-- * oplax product: 'combine' unzips a record of 'Pair's, and is inverse to the
--   covariant product 'combine'.
--
-- The covariant product also gets a laws pass (associativity, both unit laws,
-- and naturality), stated through @kindly-functors@' rank-2 'bmap1' with
-- associators and unitors written inline. This doubles as an interop check that
-- 'combine' commutes with 'bmap1'. The associators/unitors would collapse into
-- the shared "Data.Bifunctor.Monoidal.Laws" machinery once the @Nat@-category
-- 'Control.Category.Tensor.Tensor' instances for 'Product' exist.
--
-- A last group relates this class to "Data.Bifunctor.Rank2.Traversable".
-- 'Rank2.sequence' must preserve the product structure: sequencing a combined
-- record gives the 'Pair' of the component sequences, and sequencing the unit
-- record gives the unit. Only covariant interpretations are checked, because
-- 'Product' is 'Data.Bifunctor.Monoidal.Monoidal' only at 'Biapplicative'
-- components.
module Data.Bifunctor.Rank2.MonoidalSpec (tests) where

--------------------------------------------------------------------------------

import Control.Category.LawsSupport (genInt)
import Data.Bifunctor.Joker (Joker (..))
import Data.Bifunctor.Product (Product (..))
import Data.Bifunctor.Rank2.Monoidal (Monoidal, Semigroupal (..), Unital (..), gcombineSum, gsplitProduct)
import Data.Bifunctor.Rank2.Traversable qualified as Rank2
import Data.Bifunctor.Sum (Sum (..))
import Data.Functor.Const (Const (..))
import Data.Functor.Contravariant (Op (..), getOp)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Data.Void (Void, absurd)
import GHC.Generics (Generic, V1)
import Hedgehog (Gen, Group (..), Property, checkSequential, forAll, property, withTests, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Kindly (CategoricalFunctor (..), Nat (..), bmap1, runNat, type (~>))
import Prelude hiding (map)

--------------------------------------------------------------------------------
-- Test types

-- | A three-field record of bifunctor values. Exercises @K1@, @M1@, and nested
-- @:*:@.
data TestHKD p = TestHKD
  { thFst :: p Int Bool,
    thSnd :: p String Int,
    thThd :: p Bool String
  }
  deriving stock (Generic)

instance Semigroupal (->) Product (,) TestHKD

instance Unital (->) (Joker Proxy) () TestHKD

instance Monoidal (->) Product (Joker Proxy) (,) () TestHKD

instance Semigroupal (->) Sum Either TestHKD where combine = gcombineSum

instance Unital (->) (Joker V1) Void TestHKD where introduce = absurd

instance Monoidal (->) Sum (Joker V1) Either Void TestHKD

instance Semigroupal Op Product (,) TestHKD where combine = Op gsplitProduct

instance Unital Op (Joker Proxy) () TestHKD where introduce = Op (const ())

instance Monoidal Op Product (Joker Proxy) (,) () TestHKD

instance Rank2.Traversable TestHKD

-- | 'TestHKD' as a @kindly-functors@ rank-2 functor, so the law properties can
-- map interpretations through it with 'bmap1'. The domain is the bifunctor
-- category, so the morphisms are nested 'Nat's.
instance CategoricalFunctor TestHKD where
  type Dom TestHKD = (->) ~> ((->) ~> (->))
  type Cod TestHKD = (->)
  map (Nat n) (TestHKD a b c) = TestHKD (runNat n a) (runNat n b) (runNat n c)

deriving stock instance (Show (p Int Bool), Show (p String Int), Show (p Bool String)) => Show (TestHKD p)

deriving stock instance (Eq (p Int Bool), Eq (p String Int), Eq (p Bool String)) => Eq (TestHKD p)

-- | A nullary constructor. Exercises @U1@ and the unit path.
data EmptyHKD (p :: Type -> Type -> Type) = EmptyHKD
  deriving stock (Generic, Show, Eq)

instance Semigroupal (->) Product (,) EmptyHKD

instance Unital (->) (Joker Proxy) () EmptyHKD

instance Monoidal (->) Product (Joker Proxy) (,) () EmptyHKD

instance Semigroupal (->) Sum Either EmptyHKD where combine = gcombineSum

instance Unital (->) (Joker V1) Void EmptyHKD where introduce = absurd

instance Monoidal (->) Sum (Joker V1) Either Void EmptyHKD

--------------------------------------------------------------------------------
-- Monomorphic call sites (fix @cat@, @tC@, @tD@ for the derived instances).

combineHKD :: TestHKD p -> TestHKD q -> TestHKD (Product p q)
combineHKD x y = combine @(->) @Product @(,) (x, y)

introduceHKD :: TestHKD (Joker Proxy)
introduceHKD = introduce @(->) @(Joker Proxy) @() ()

combineSumHKD :: Either (TestHKD p) (TestHKD q) -> TestHKD (Sum p q)
combineSumHKD = combine @(->) @Sum @Either

splitHKD :: TestHKD (Product p q) -> (TestHKD p, TestHKD q)
splitHKD = getOp (combine @Op @Product @(,))

-- | Map a bifunctor natural transformation over every field, through kindly's
-- rank-2 functor interface.
mapHKD :: (forall x y. p x y -> q x y) -> TestHKD p -> TestHKD q
mapHKD n = bmap1 (Nat n)

-- | The reference for the covariant product 'combine': field-wise 'Pair'.
refCombine :: TestHKD p -> TestHKD q -> TestHKD (Product p q)
refCombine (TestHKD a b c) (TestHKD a' b' c') =
  TestHKD (Pair a a') (Pair b b') (Pair c c')

-- | The reference for the coproduct 'combine': every field on one side.
refCombineSum :: Either (TestHKD p) (TestHKD q) -> TestHKD (Sum p q)
refCombineSum (Left (TestHKD a b c)) = TestHKD (L2 a) (L2 b) (L2 c)
refCombineSum (Right (TestHKD a b c)) = TestHKD (R2 a) (R2 b) (R2 c)

--------------------------------------------------------------------------------
-- Associators and unitors for the 'Product' tensor on the bifunctor category.
-- These stand in for the (as yet unwritten) @Nat@-category 'Tensor' instances.

-- | 'Product'\'s action on morphisms of the bifunctor category.
prodNat ::
  (forall x y. p x y -> p' x y) ->
  (forall x y. q x y -> q' x y) ->
  Product p q a b ->
  Product p' q' a b
prodNat l r (Pair p q) = Pair (l p) (r q)

-- | The associator of 'Product' on the bifunctor category.
assocProd :: Product p (Product q r) a b -> Product (Product p q) r a b
assocProd (Pair a (Pair b c)) = Pair (Pair a b) c

-- | The right unitor: @'Joker' 'Proxy'@ is the unit of 'Product'.
runitProd :: Product p (Joker Proxy) a b -> p a b
runitProd (Pair a _) = a

-- | The left unitor.
lunitProd :: Product (Joker Proxy) p a b -> p a b
lunitProd (Pair _ a) = a

--------------------------------------------------------------------------------
-- Natural transformations between the interpretations used by the laws.

-- | Keep the first component, discard the second.
pairToConst :: (a, b) -> Const a b
pairToConst (a, _) = Const a

-- | Inject the first component on the left.
pairToEither :: (a, b) -> Either a b
pairToEither (a, _) = Left a

--------------------------------------------------------------------------------
-- Generators

genString :: Gen String
genString = Gen.string (Range.linear 0 5) Gen.alpha

-- | Build a 'TestHKD' generator from a per-field wrapper.
genHKD :: (forall a b. Gen a -> Gen b -> Gen (p a b)) -> Gen (TestHKD p)
genHKD f = TestHKD <$> f genInt Gen.bool <*> f genString genInt <*> f Gen.bool genString

genPairHKD :: Gen (TestHKD (,))
genPairHKD = genHKD (\ga gb -> (,) <$> ga <*> gb)

genEitherHKD :: Gen (TestHKD Either)
genEitherHKD = genHKD (\ga gb -> Gen.choice [Left <$> ga, Right <$> gb])

genConstHKD :: Gen (TestHKD Const)
genConstHKD = genHKD (\ga _ -> Const <$> ga)

genProductHKD :: Gen (TestHKD (Product (,) Either))
genProductHKD =
  genHKD (\ga gb -> Pair <$> ((,) <$> ga <*> gb) <*> Gen.choice [Left <$> ga, Right <$> gb])

-- | A record of 'Pair's with 'Biapplicative' components, so 'Rank2.sequence'
-- applies at the 'Product' interpretation.
genPairConstHKD :: Gen (TestHKD (Product (,) Const))
genPairConstHKD =
  genHKD (\ga gb -> Pair <$> ((,) <$> ga <*> gb) <*> (Const <$> ga))

--------------------------------------------------------------------------------
-- Covariant product: agreement with the reference

-- | 'combine' agrees with the hand-written field-wise 'Pair'.
combineAgreesWithRef :: Property
combineAgreesWithRef = property $ do
  x <- forAll genPairHKD
  y <- forAll genEitherHKD
  combineHKD x y === refCombine x y

-- | 'combine' at a homogeneous interpretation also agrees with the reference.
combineAgreesWithRefHomogeneous :: Property
combineAgreesWithRefHomogeneous = property $ do
  x <- forAll genPairHKD
  y <- forAll genPairHKD
  combineHKD x y === refCombine x y

-- | 'introduce' fills every field with the unit bifunctor.
introduceIsAllUnit :: Property
introduceIsAllUnit = withTests 1 $ property $ do
  introduceHKD === TestHKD (Joker Proxy) (Joker Proxy) (Joker Proxy)

--------------------------------------------------------------------------------
-- Covariant product: monoidal laws (via kindly's rank-2 'bmap1')

-- | Naturality: 'combine' commutes with maps into either tensor position.
-- Doubles as the interop check that 'combine' commutes with 'bmap1'.
naturalityLaw :: Property
naturalityLaw = property $ do
  x <- forAll genPairHKD
  y <- forAll genPairHKD
  mapHKD (prodNat pairToConst pairToEither) (combineHKD x y)
    === combineHKD (mapHKD pairToConst x) (mapHKD pairToEither y)

-- | Associativity: reassociating the domain 'Product' turns the right-nested
-- 'combine' into the left-nested one.
associativityLaw :: Property
associativityLaw = property $ do
  x <- forAll genPairHKD
  y <- forAll genEitherHKD
  z <- forAll genConstHKD
  mapHKD assocProd (combineHKD x (combineHKD y z))
    === combineHKD (combineHKD x y) z

-- | Right unit: combining with @'introduce' ()@ and projecting recovers the record.
rightUnitLaw :: Property
rightUnitLaw = property $ do
  x <- forAll genPairHKD
  mapHKD runitProd (combineHKD x introduceHKD) === x

-- | Left unit: the mirror of 'rightUnitLaw'.
leftUnitLaw :: Property
leftUnitLaw = property $ do
  x <- forAll genPairHKD
  mapHKD lunitProd (combineHKD introduceHKD x) === x

--------------------------------------------------------------------------------
-- Coproduct

-- | Injecting on the left sends every field to 'L2'.
coproductInjectsLeft :: Property
coproductInjectsLeft = property $ do
  x <- forAll genPairHKD
  let e = Left x :: Either (TestHKD (,)) (TestHKD Either)
  combineSumHKD e === refCombineSum e

-- | Injecting on the right sends every field to 'R2'.
coproductInjectsRight :: Property
coproductInjectsRight = property $ do
  y <- forAll genEitherHKD
  let e = Right y :: Either (TestHKD (,)) (TestHKD Either)
  combineSumHKD e === refCombineSum e

--------------------------------------------------------------------------------
-- Oplax product (split)

-- | Split then combine is the identity (product iso, one direction).
splitAfterCombine :: Property
splitAfterCombine = property $ do
  x <- forAll genPairHKD
  y <- forAll genEitherHKD
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
  combine @(->) @Product @(,) (EmptyHKD :: EmptyHKD (,), EmptyHKD :: EmptyHKD Either) === EmptyHKD
  introduce @(->) @(Joker Proxy) @() () === (EmptyHKD :: EmptyHKD (Joker Proxy))
  combine @(->) @Sum @Either (Left EmptyHKD :: Either (EmptyHKD (,)) (EmptyHKD Either)) === EmptyHKD

--------------------------------------------------------------------------------
-- Coherence with Rank2.Traversable

-- TODO: Check the profunctor interpretation too. That needs a
-- variance-agnostic 'Data.Bifunctor.Monoidal.Monoidal' instance for 'Product'.

-- | Sequencing a combined record gives the 'Pair' of the component sequences.
sequencePreservesProduct :: Property
sequencePreservesProduct = property $ do
  x <- forAll genPairHKD
  y <- forAll genConstHKD
  Rank2.sequence (combineHKD x y) === Pair (Rank2.sequence x) (Rank2.sequence y)

-- | Sequencing the unit record gives the unit bifunctor.
sequencePreservesUnit :: Property
sequencePreservesUnit = withTests 1 $ property $ do
  Rank2.sequence introduceHKD === Joker Proxy

-- | Sequencing a record of 'Pair's agrees with splitting it first and
-- sequencing each half.
sequenceAgreesWithSplit :: Property
sequenceAgreesWithSplit = property $ do
  z <- forAll genPairConstHKD
  let (x, y) = splitHKD z
  Rank2.sequence z === Pair (Rank2.sequence x) (Rank2.sequence y)

--------------------------------------------------------------------------------

tests :: IO Bool
tests =
  checkSequential $
    Group
      "Data.Bifunctor.Rank2.Monoidal"
      [ ("combine agrees with reference ((,)/Either)", combineAgreesWithRef),
        ("combine agrees with reference ((,))", combineAgreesWithRefHomogeneous),
        ("introduce is all Joker Proxy", introduceIsAllUnit),
        ("naturality (combine commutes with bmap1)", naturalityLaw),
        ("associativity", associativityLaw),
        ("right unit", rightUnitLaw),
        ("left unit", leftUnitLaw),
        ("coproduct injects left", coproductInjectsLeft),
        ("coproduct injects right", coproductInjectsRight),
        ("split . combine = id", splitAfterCombine),
        ("combine . split = id", combineAfterSplit),
        ("empty record at every instantiation", emptyRecord),
        ("sequence preserves the product", sequencePreservesProduct),
        ("sequence preserves the unit", sequencePreservesUnit),
        ("sequence agrees with split", sequenceAgreesWithSplit)
      ]
