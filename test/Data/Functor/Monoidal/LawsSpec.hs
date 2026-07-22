{-# LANGUAGE OverloadedStrings #-}

-- | Self-test: run the exported 'Laws' against known-good library instances,
-- both covariant ('Maybe', @[]@) and contravariant ('Predicate'), so the
-- sublibrary's law statements are exercised end-to-end. This includes the
-- variance-agnostic 'Data.Functor.Product.Product' instance, law-checked at
-- /both/ variances from the single delegating instance: @Product Maybe []@
-- covariantly and @Product Predicate Predicate@ contravariantly.
module Data.Functor.Monoidal.LawsSpec (tests) where

--------------------------------------------------------------------------------

import Data.Functor.Const (Const (..))
import Data.Functor.Contravariant (Op (..), Predicate (..))
import Data.Functor.Monoidal (Semigroupal (..))
import Data.Functor.Monoidal.Laws
  ( contravariantMonoidalLaws,
    monoidalLaws,
    opSemigroupalLaws,
    representableSplitLaws,
    semigroupalLaws,
    unitalLaws,
  )
import Data.Functor.Product (Product)
import Data.Functor.Product qualified as Product
import Data.Functor.Reverse (Reverse (..))
import Data.Monoid (Sum (..))
import Data.String (fromString)
import Data.Void (Void)
import GHC.Generics ((:*:) (..))
import Hedgehog (Gen, Group (..), Property, PropertyName, checkSequential)
import Hedgehog.Classes (Laws (..), lawsCheck)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude

--------------------------------------------------------------------------------

genInt :: Gen Int
genInt = Gen.int (Range.linear (-100) 100)

-- Covariant witnesses.

genMaybe :: Gen a -> Gen (Maybe a)
genMaybe = Gen.maybe

genList :: Gen a -> Gen [a]
genList = Gen.list (Range.linear 0 4)

-- Contravariant witness: 'Predicate' is Divisible (at @(,)@) and Decidable (at
-- @Either@). It has no 'Eq' \/ 'Show', so it is observed by running it.

genPredicate :: Gen (Predicate Int)
genPredicate = (\n -> Predicate (> n)) <$> genInt

obsPredicate :: Predicate a -> a -> Bool
obsPredicate (Predicate p) = p

genPairT :: Gen a -> Gen b -> Gen (a, b)
genPairT ga gb = (,) <$> ga <*> gb

genEitherT :: Gen a -> Gen b -> Gen (Either a b)
genEitherT ga gb = Gen.choice [Left <$> ga, Right <$> gb]

-- Op (comonoidal) witness: a pair functor whose split is the unzip.

data Pair a = Pair a a deriving (Functor, Show, Eq)

instance Semigroupal (->) (,) (,) Pair where
  combine (Pair a b, Pair c d) = Pair (a, c) (b, d)

instance Semigroupal Op (,) (,) Pair where
  combine = Op (\(Pair (a, b) (c, d)) -> (Pair a c, Pair b d))

genPairF :: Gen a -> Gen (Pair a)
genPairF g = Pair <$> g <*> g

-- Product witnesses: the single variance-agnostic 'Product' instance, exercised
-- at both variances. Covariant when its components are ('Maybe', @[]@), compared
-- with 'Eq'; contravariant when they are ('Predicate'), observed through @obs@.

genProductCov :: Gen a -> Gen (Product Maybe [] a)
genProductCov g = Product.Pair <$> genMaybe g <*> genList g

genProductCon :: Gen (Product Predicate Predicate Int)
genProductCon = Product.Pair <$> genPredicate <*> genPredicate

obsProductCon :: Product Predicate Predicate a -> a -> (Bool, Bool)
obsProductCon (Product.Pair p q) a = (obsPredicate p a, obsPredicate q a)

-- Generic product ':*:' (componentwise, like Product), at both variances.

genGenProdCov :: Gen a -> Gen ((Maybe :*: []) a)
genGenProdCov g = (:*:) <$> genMaybe g <*> genList g

genGenProdCon :: Gen ((Predicate :*: Predicate) Int)
genGenProdCon = (:*:) <$> genPredicate <*> genPredicate

obsGenProdCon :: (Predicate :*: Predicate) a -> a -> (Bool, Bool)
obsGenProdCon (p :*: q) a = (obsPredicate p a, obsPredicate q a)

-- Phantom 'Const': one instance for every tensor and both variances, combine is
-- the underlying 'Semigroup'. Compared with 'Eq'.

genConst :: Gen a -> Gen (Const (Sum Int) a)
genConst _ = Const . Sum <$> genInt

-- Transparent wrapper 'Reverse' (inherits its component by coercion), both
-- variances.

genReverseCov :: Gen a -> Gen (Reverse Maybe a)
genReverseCov g = Reverse <$> genMaybe g

genReverseCon :: Gen (Reverse Predicate Int)
genReverseCon = Reverse <$> genPredicate

obsReverseCon :: Reverse Predicate a -> a -> Bool
obsReverseCon (Reverse p) a = obsPredicate p a

--------------------------------------------------------------------------------

-- | Splice a sublibrary 'Laws' into the hedgehog 'Group', prefixing each of its
-- properties with the instance under test.
labeled :: String -> Laws -> [(PropertyName, Property)]
labeled prefix ls = [(fromString (prefix <> " " <> n), p) | (n, p) <- lawsProperties ls]

tests :: IO Bool
tests = do
  cov <-
    checkSequential $
      Group "Covariant" $
        concat
          [ -- Covariant.
            labeled "Maybe (,)" (monoidalLaws @(,) @() genMaybe),
            labeled "List (,)" (monoidalLaws @(,) @() genList),
            labeled "Maybe Either" (monoidalLaws @Either @Void genMaybe),
            labeled "List Either" (semigroupalLaws @Either genList),
            labeled "List (,)" (unitalLaws @(,) @() genList),
            -- Product, covariant components: one delegating instance, both tensors.
            labeled "Product (,)" (monoidalLaws @(,) @() genProductCov),
            labeled "Product Either" (monoidalLaws @Either @Void genProductCov),
            -- Generic product ':*:', phantom 'Const', and transparent wrapper 'Reverse'.
            labeled ":*: (,)" (monoidalLaws @(,) @() genGenProdCov),
            labeled ":*: Either" (monoidalLaws @Either @Void genGenProdCov),
            labeled "Const (,)" (monoidalLaws @(,) @() genConst),
            labeled "Const Either" (monoidalLaws @Either @Void genConst),
            labeled "Reverse (,)" (monoidalLaws @(,) @() genReverseCov)
          ]
  con <-
    checkSequential $
      Group "Contravariant" $
        concat
          [ -- Contravariant.
            labeled "Predicate (,)" (contravariantMonoidalLaws @(,) @() genPredicate genPairT obsPredicate),
            labeled "Predicate Either" (contravariantMonoidalLaws @Either @Void genPredicate genEitherT obsPredicate),
            -- Product, contravariant components: the same instance, other variance.
            labeled "Product (,)" (contravariantMonoidalLaws @(,) @() genProductCon genPairT obsProductCon),
            labeled "Product Either" (contravariantMonoidalLaws @Either @Void genProductCon genEitherT obsProductCon),
            -- Generic product ':*:' and transparent wrapper 'Reverse', contravariant.
            labeled ":*: (,)" (contravariantMonoidalLaws @(,) @() genGenProdCon genPairT obsGenProdCon),
            labeled ":*: Either" (contravariantMonoidalLaws @Either @Void genGenProdCon genEitherT obsGenProdCon),
            labeled "Reverse (,)" (contravariantMonoidalLaws @(,) @() genReverseCon genPairT obsReverseCon),
            -- Op (comonoidal) split.
            labeled "Pair" (opSemigroupalLaws genPairF),
            labeled "Pair" (representableSplitLaws genPairF)
          ]
  pure (and [cov, con])
