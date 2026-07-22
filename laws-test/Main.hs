-- | Self-test: run the exported 'Laws' against known-good library instances,
-- both covariant ('Maybe', @[]@) and contravariant ('Predicate'), so the
-- sublibrary's law statements are exercised end-to-end.
module Main (main) where

import Control.Monad (unless)
import Data.Functor.Contravariant (Op (..), Predicate (..))
import Data.Functor.Monoidal (Semigroupal (..))
import Data.Functor.Monoidal.Laws
  ( contravariantMonoidalLaws,
    monoidalLaws,
    opSemigroupalLaws,
    semigroupalLaws,
    unitalLaws,
  )
import Data.Void (Void)
import Hedgehog (Gen)
import Hedgehog.Classes (lawsCheck)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import System.Exit (exitFailure)
import Prelude

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

instance Semigroupal Op (,) (,) Pair where
  combine = Op (\(Pair (a, b) (c, d)) -> (Pair a c, Pair b d))

genPairF :: Gen a -> Gen (Pair a)
genPairF g = Pair <$> g <*> g

main :: IO ()
main = do
  oks <-
    sequence
      [ -- Covariant.
        lawsCheck (monoidalLaws @(,) @() genMaybe),
        lawsCheck (monoidalLaws @(,) @() genList),
        lawsCheck (monoidalLaws @Either @Void genMaybe),
        lawsCheck (semigroupalLaws @Either genList),
        lawsCheck (unitalLaws @(,) @() genList),
        -- Contravariant.
        lawsCheck (contravariantMonoidalLaws @(,) @() genPredicate genPairT obsPredicate),
        lawsCheck (contravariantMonoidalLaws @Either @Void genPredicate genEitherT obsPredicate),
        -- Op (comonoidal) split.
        lawsCheck (opSemigroupalLaws genPairF)
      ]
  unless (and oks) exitFailure
