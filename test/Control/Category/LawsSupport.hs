{-# LANGUAGE OverloadedStrings #-}

-- | Shared scaffolding for the "Control.Category.Tensor.Laws" and
-- "Control.Category.Cartesian.Laws" self-tests. Provides the extensional
-- observers for each category, the witness generators, and the 'labeled' splice
-- that folds a sublibrary 'Laws' into a hedgehog 'Group'.
module Control.Category.LawsSupport
  ( -- * Observers
    runFun,
    runOp,
    runIso,
    runStarMaybe,
    runKleisliMaybe,

    -- * Generators
    genInt,
    genBool,
    genTPair,
    genTEither,
    genTThese,

    -- * Group assembly
    labeled,
  )
where

--------------------------------------------------------------------------------

import Control.Arrow (Kleisli (..))
import Control.Category.Tensor (Iso (..))
import Data.Functor.Contravariant (Op (..))
import Data.Functor.Identity (Identity (..))
import Data.Profunctor (Star (..))
import Data.String (fromString)
import Data.These (These (..))
import Hedgehog (Gen, Property, PropertyName)
import Hedgehog.Classes (Laws (..))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude

--------------------------------------------------------------------------------
-- Extensional observers. Run a morphism on an input to get a comparable result.

runFun :: (a -> b) -> a -> Identity b
runFun f = Identity . f

runOp :: Op a b -> b -> Identity a
runOp o = Identity . getOp o

runIso :: Iso (->) a b -> a -> Identity b
runIso i = Identity . fwd i

runStarMaybe :: Star Maybe a b -> a -> Maybe b
runStarMaybe = runStar

runKleisliMaybe :: Kleisli Maybe a b -> a -> Maybe b
runKleisliMaybe = runKleisli

--------------------------------------------------------------------------------
-- Generators. The @genT*@ builders are rank-2, used to assemble the nested
-- witnesses the structure laws need.

genInt :: Gen Int
genInt = Gen.int (Range.linear (-100) 100)

genBool :: Gen Bool
genBool = Gen.bool

genTPair :: Gen x -> Gen y -> Gen (x, y)
genTPair gx gy = (,) <$> gx <*> gy

genTEither :: Gen x -> Gen y -> Gen (Either x y)
genTEither gx gy = Gen.choice [Left <$> gx, Right <$> gy]

genTThese :: Gen x -> Gen y -> Gen (These x y)
genTThese gx gy = Gen.choice [This <$> gx, That <$> gy, These <$> gx <*> gy]

--------------------------------------------------------------------------------

-- | Splice a sublibrary 'Laws' into the hedgehog 'Group', prefixing each of its
-- properties with the instance under test.
labeled :: String -> Laws -> [(PropertyName, Property)]
labeled prefix ls = [(fromString (prefix <> " " <> n), p) | (n, p) <- lawsProperties ls]
