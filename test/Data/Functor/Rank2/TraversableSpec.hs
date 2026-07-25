{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Exercises the generically derived rank-2 'Rank2.Traversable' for
-- functor-interpreted HKDs. At a covariant 'Applicative' interpretation
-- (@cat ~ (->)@) 'Rank2.sequence' must agree with the hand-written applicative
-- traversal, respect the 'Identity' law, and commute with applicative
-- homomorphisms. At a contravariant 'Predicate' interpretation (@cat ~ Op@,
-- 'Divisible') it must conjoin the field predicates.
module Data.Functor.Rank2.TraversableSpec (tests) where

--------------------------------------------------------------------------------

import Control.Category.LawsSupport (genInt)
import Data.Functor.Compose (Compose (..))
import Data.Functor.Contravariant (Predicate (..))
import Data.Functor.Identity (Identity (..))
import Data.Functor.Monoidal (Monoidal)
import Data.Functor.Rank2.Traversable qualified as Rank2
import Data.Kind (Type)
import Kindly qualified
import Data.Maybe (maybeToList)
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
  deriving anyclass (Rank2.Traversable)

deriving stock instance (Show (f Int), Show (f Bool), Show (f String)) => Show (TestHKD f)

deriving stock instance (Eq (f Int), Eq (f Bool), Eq (f String)) => Eq (TestHKD f)

-- | A nullary constructor. Exercises @U1@ and the 'introduce' path.
data EmptyHKD (f :: Type -> Type) = EmptyHKD
  deriving stock (Generic, Show, Eq)
  deriving anyclass (Rank2.Traversable)

-- | The reference: sequencing an HKD through an 'Applicative' is the
-- field-wise applicative traversal, left to right.
refSequence :: (Applicative f) => TestHKD f -> f (TestHKD Identity)
refSequence (TestHKD a b c) =
  (\x y z -> TestHKD (Identity x) (Identity y) (Identity z)) <$> a <*> b <*> c

--------------------------------------------------------------------------------
-- Generators

genString :: Gen String
genString = Gen.string (Range.linear 0 5) Gen.alpha

-- | Build a 'TestHKD' generator from a per-field wrapper.
genHKD :: (forall a. Gen a -> Gen (f a)) -> Gen (TestHKD f)
genHKD f = TestHKD <$> f genInt <*> f Gen.bool <*> f genString

genIdentityHKD :: Gen (TestHKD Identity)
genIdentityHKD = genHKD (fmap Identity)

genMaybeHKD :: Gen (TestHKD Maybe)
genMaybeHKD = genHKD Gen.maybe

genListHKD :: Gen (TestHKD [])
genListHKD = genHKD (Gen.list (Range.linear 0 3))

genComposeHKD :: Gen (TestHKD (Compose Maybe []))
genComposeHKD = genHKD (fmap Compose . Gen.maybe . Gen.list (Range.linear 0 3))

--------------------------------------------------------------------------------
-- Properties

-- | Sequencing at 'Identity' is 'Identity'.
identityLaw :: Property
identityLaw = property $ do
  hkd <- forAll genIdentityHKD
  Rank2.sequence hkd === Identity hkd

-- | Agreement with the reference traversal at a given interpretation.
agreesWithRef ::
  ( Applicative f,
    Kindly.Functor (->) f,
    Monoidal (->) (,) () (,) () f,
    Show (f Int),
    Show (f Bool),
    Show (f String),
    Eq (f (TestHKD Identity)),
    Show (f (TestHKD Identity))
  ) =>
  Gen (TestHKD f) ->
  Property
agreesWithRef gen = property $ do
  hkd <- forAll gen
  Rank2.sequence hkd === refSequence hkd

-- | 'maybeToList' is an applicative homomorphism, so sequencing must commute
-- with it (naturality).
naturality :: Property
naturality = property $ do
  hkd <- forAll genMaybeHKD
  let hoist (TestHKD a b c) = TestHKD (maybeToList a) (maybeToList b) (maybeToList c)
  maybeToList (Rank2.sequence hkd) === Rank2.sequence (hoist hkd)

-- | A field-less record sequences to 'pure' via 'introduce'.
emptySequencesToPure :: Property
emptySequencesToPure = withTests 1 $ property $ do
  Rank2.sequence (EmptyHKD :: EmptyHKD Maybe) === Just EmptyHKD
  Rank2.sequence (EmptyHKD :: EmptyHKD []) === [EmptyHKD]

--------------------------------------------------------------------------------
-- Contravariant interpretation

-- | The reference for the contravariant 'Predicate' interpretation: sequencing
-- a record of per-field predicates through 'Divisible' conjoins them, so the
-- whole record passes iff every field's predicate passes on its own value.
refPredicate :: TestHKD Predicate -> Predicate (TestHKD Identity)
refPredicate (TestHKD pInt pBool pString) =
  Predicate $ \(TestHKD (Identity i) (Identity b) (Identity s)) ->
    getPredicate pInt i && getPredicate pBool b && getPredicate pString s

-- | 'Rank2.sequence' at the contravariant 'Predicate' interpretation
-- (@cat ~ Op@, 'Divisible') must agree with the conjunction reference.
-- Predicates have no 'Eq', so they are compared extensionally by observing
-- them on a generated record. The predicate parameters are generated (rather
-- than the predicates themselves) so 'forAll' has something to show.
agreesWithRefPredicate :: Property
agreesWithRefPredicate = property $ do
  n <- forAll genInt
  b <- forAll Gen.bool
  k <- forAll (Gen.int (Range.linear 0 5))
  input <- forAll genIdentityHKD
  let preds = TestHKD (Predicate (< n)) (Predicate (== b)) (Predicate ((<= k) . length))
  getPredicate (Rank2.sequence preds) input === getPredicate (refPredicate preds) input

-- | A field-less record sequences to 'conquer', the always-true predicate.
emptyPredicateIsConquer :: Property
emptyPredicateIsConquer = withTests 1 $ property $ do
  getPredicate (Rank2.sequence (EmptyHKD :: EmptyHKD Predicate)) EmptyHKD === True

--------------------------------------------------------------------------------

tests :: IO Bool
tests =
  checkSequential $
    Group
      "Data.Functor.Rank2.Traversable"
      [ ("identity law", identityLaw),
        ("agrees with reference (Maybe)", agreesWithRef genMaybeHKD),
        ("agrees with reference ([])", agreesWithRef genListHKD),
        ("agrees with reference (Compose Maybe [])", agreesWithRef genComposeHKD),
        ("naturality of maybeToList", naturality),
        ("empty record sequences to pure", emptySequencesToPure),
        ("agrees with reference (Predicate)", agreesWithRefPredicate),
        ("empty record is conquer (Predicate)", emptyPredicateIsConquer)
      ]
