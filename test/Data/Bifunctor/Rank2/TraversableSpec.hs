{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}

-- | Exercises the generically derived rank-2 'Rank2.Traversable' for
-- bifunctor-interpreted HKDs. Sequencing a record of @p a b@ fields yields
-- @p (hkd 'Rank2.First') (hkd 'Rank2.Second')@, which must act field-wise. The
-- profunctor case (@(Op, (->))@) is checked against an applicative reference.
-- The covariant case (@((->), (->))@) is the 'Biapplicative' unzip.
module Data.Bifunctor.Rank2.TraversableSpec (tests) where

--------------------------------------------------------------------------------

import Control.Arrow (Kleisli (..))
import Control.Category.LawsSupport (genInt)
import Data.Bifunctor.Rank2.Traversable qualified as Rank2
import Data.Kind (Type)
import GHC.Generics (Generic)
import Hedgehog (Gen, Group (..), Property, checkSequential, forAll, property, withTests, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude

--------------------------------------------------------------------------------
-- Test types

-- | A three-field record of profunctor values. Exercises @K1@, @M1@, and
-- nested @:*:@.
data TestHKD p = TestHKD
  { thFun :: p Int Bool,
    thLen :: p String Int,
    thFlag :: p Bool String
  }
  deriving stock (Generic)
  deriving anyclass (Rank2.Traversable)

deriving stock instance (Show (p Int Bool), Show (p String Int), Show (p Bool String)) => Show (TestHKD p)

deriving stock instance (Eq (p Int Bool), Eq (p String Int), Eq (p Bool String)) => Eq (TestHKD p)

-- | A nullary constructor. Exercises @U1@ and the 'introduce' path.
data EmptyHKD (p :: Type -> Type -> Type) = EmptyHKD
  deriving stock (Generic, Show, Eq)
  deriving anyclass (Rank2.Traversable)

--------------------------------------------------------------------------------
-- Generators

genString :: Gen String
genString = Gen.string (Range.linear 0 5) Gen.alpha

-- | A record of pairs, for the covariant @(,)@ (Biapplicative) instantiation.
genPairHKD :: Gen (TestHKD (,))
genPairHKD =
  TestHKD
    <$> ((,) <$> genInt <*> Gen.bool)
    <*> ((,) <$> genString <*> genInt)
    <*> ((,) <$> Gen.bool <*> genString)

--------------------------------------------------------------------------------
-- Properties

-- | Sequencing a record of functions gives a function between records that
-- applies each field pointwise.
functionActsFieldwise :: Property
functionActsFieldwise = property $ do
  k <- forAll genInt
  m <- forAll genInt
  let hkd = TestHKD {thFun = \n -> n > k, thLen = \s -> length s + m, thFlag = \b -> if b then show k else show m}
      run = Rank2.sequence hkd
  a <- forAll genInt
  s <- forAll genString
  b <- forAll Gen.bool
  run (TestHKD (Rank2.First a) (Rank2.First s) (Rank2.First b))
    === TestHKD (Rank2.Second (a > k)) (Rank2.Second (length s + m)) (Rank2.Second (if b then show k else show m))

-- | Sequencing a record of 'Kleisli' arrows combines the effects field-wise,
-- agreeing with the applicative reference.
kleisliAgrees :: Property
kleisliAgrees = property $ do
  k <- forAll genInt
  m <- forAll genInt
  let f n = if n > k then Just (even n) else Nothing
      g s = if length s > m then Just (length s) else Nothing
      h b = if b then Just (show k) else Nothing
      hkd = TestHKD (Kleisli f) (Kleisli g) (Kleisli h)
  a <- forAll genInt
  s <- forAll genString
  b <- forAll Gen.bool
  runKleisli (Rank2.sequence hkd) (TestHKD (Rank2.First a) (Rank2.First s) (Rank2.First b))
    === ((\x y z -> TestHKD (Rank2.Second x) (Rank2.Second y) (Rank2.Second z)) <$> f a <*> g s <*> h b)

-- | At @Kleisli []@ the effect order is observable: 'Maybe' cannot tell a
-- flipped combine apart, but the cartesian product of multi-element lists
-- pins the left-to-right ordering against the applicative reference.
kleisliOrdersEffects :: Property
kleisliOrdersEffects = property $ do
  k <- forAll genInt
  let f n = [even n, n > k]
      g s = [length s, length s + k]
      h b = [show b, show (b, k)]
      hkd = TestHKD (Kleisli f) (Kleisli g) (Kleisli h)
  a <- forAll genInt
  s <- forAll genString
  b <- forAll Gen.bool
  runKleisli (Rank2.sequence hkd) (TestHKD (Rank2.First a) (Rank2.First s) (Rank2.First b))
    === ((\x y z -> TestHKD (Rank2.Second x) (Rank2.Second y) (Rank2.Second z)) <$> f a <*> g s <*> h b)

-- | At the covariant bifunctor @(,)@ sequencing is the 'Biapplicative' unzip:
-- a record of pairs splits into the record of first components and the record
-- of second components.
pairUnzips :: Property
pairUnzips = property $ do
  hkd <- forAll genPairHKD
  let TestHKD (a1, b1) (a2, b2) (a3, b3) = hkd
  Rank2.sequence hkd
    === ( TestHKD (Rank2.First a1) (Rank2.First a2) (Rank2.First a3),
          TestHKD (Rank2.Second b1) (Rank2.Second b2) (Rank2.Second b3)
        )

-- | A field-less record sequences to the unit of the profunctor via
-- 'introduce'.
emptySequencesToUnit :: Property
emptySequencesToUnit = withTests 1 $ property $ do
  Rank2.sequence (EmptyHKD :: EmptyHKD (->)) EmptyHKD === EmptyHKD
  runKleisli (Rank2.sequence (EmptyHKD :: EmptyHKD (Kleisli Maybe))) EmptyHKD === Just EmptyHKD

--------------------------------------------------------------------------------

tests :: IO Bool
tests =
  checkSequential $
    Group
      "Data.Bifunctor.Rank2.Traversable"
      [ ("function sequencing acts field-wise", functionActsFieldwise),
        ("Kleisli sequencing agrees with reference", kleisliAgrees),
        ("Kleisli sequencing orders effects left-to-right", kleisliOrdersEffects),
        ("record of pairs unzips (Biapplicative)", pairUnzips),
        ("empty record sequences to unit", emptySequencesToUnit)
      ]
