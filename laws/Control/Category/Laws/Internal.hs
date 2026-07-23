-- | Internal shared machinery for the @Control.Category.*.Laws@ modules.
--
-- Morphisms in the categories these law modules target ('(->)', @'Star' m@,
-- @'Kleisli' m@, 'Op') have no 'Eq' \/ 'Show', so every law is checked
-- /extensionally/. Build both sides, run them on a generated input through a
-- caller-supplied observer, and compare the observed results. 'agree' is that
-- primitive. 'genInt' \/ 'genBool' are the witness element types the
-- coherence squares are checked at.
module Control.Category.Laws.Internal
  ( genInt,
    genBool,
    agree,
  )
where

--------------------------------------------------------------------------------

import Hedgehog (Gen, Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude

--------------------------------------------------------------------------------

-- | The witness element types the coherence squares are checked at.
genInt :: Gen Int
genInt = Gen.int (Range.linear (-100) 100)

genBool :: Gen Bool
genBool = Gen.bool

-- | Observe that two parallel morphisms agree on a generated input. @run@ is the
-- caller's extensional observer for the category. For example,
-- @('Data.Functor.Identity.Identity' '.') . ($)@ for @('->')@, @runStar@ \/
-- @runKleisli@ for the Kleisli-style categories.
agree ::
  (Eq (obs y), Show (obs y), Show x) =>
  (cat x y -> x -> obs y) ->
  cat x y ->
  cat x y ->
  Gen x ->
  Property
agree run f g gen = property $ do
  x <- forAll gen
  run f x === run g x
