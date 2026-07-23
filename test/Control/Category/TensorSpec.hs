{-# LANGUAGE OverloadedStrings #-}

-- | Run the exported "Control.Category.Tensor.Laws" 'Laws' against the
-- instances the library ships for 'GBifunctor', 'Iso', 'Associative', 'Tensor',
-- and 'Symmetric', over every category that carries them. The categories are
-- @('->')@, 'Op', @'Iso' ('->')@, and @'Star' 'Maybe'@ \/ @'Kleisli' 'Maybe'@.
module Control.Category.TensorSpec (tests) where

--------------------------------------------------------------------------------

import Control.Arrow (Kleisli (..))
import Control.Category.LawsSupport
  ( genBool,
    genInt,
    genTEither,
    genTPair,
    genTThese,
    labeled,
    runFun,
    runIso,
    runKleisliMaybe,
    runOp,
    runStarMaybe,
  )
import Control.Category.Tensor (GBifunctor, Iso (..))
import Control.Category.Tensor.Laws
  ( associativeLaws,
    gbifunctorLaws,
    isoLaws,
    symmetricLaws,
    tensorLaws,
  )
import Data.Functor.Contravariant (Op (..))
import Data.Profunctor (Star (..))
import Data.These (These (..))
import Data.Void (Void)
import Hedgehog (Gen, Group (..), Property, PropertyName, checkSequential)
import Prelude

--------------------------------------------------------------------------------
-- Pre-built witnesses for the GBifunctor arrows.

genPairInt :: Gen (Int, Int)
genPairInt = genTPair genInt genInt

genEitherInt :: Gen (Either Int Int)
genEitherInt = genTEither genInt genInt

genTheseInt :: Gen (These Int Int)
genTheseInt = genTThese genInt genInt

--------------------------------------------------------------------------------
-- Endo-arrows per tensor factor, one pair for each category with a GBifunctor
-- instance. The 'Maybe' arrows include a failing branch so the effect is
-- exercised.

funLeft, funRight :: (Int -> Int, Int -> Int)
funLeft = ((+ 1), (* 2))
funRight = (subtract 3, negate)

opLeft, opRight :: (Op Int Int, Op Int Int)
opLeft = (Op (+ 1), Op (* 2))
opRight = (Op (subtract 3), Op negate)

isoLeft, isoRight :: (Iso (->) Int Int, Iso (->) Int Int)
isoLeft = (Iso (+ 1) (subtract 1), Iso (* 2) (`div` 2))
isoRight = (Iso (subtract 3) (+ 3), Iso negate negate)

starMaybeLeft, starMaybeRight :: (Star Maybe Int Int, Star Maybe Int Int)
starMaybeLeft = (Star (\x -> Just (x + 1)), Star (\x -> if even x then Just (x * 2) else Nothing))
starMaybeRight = (Star (\x -> Just (x - 3)), Star (\x -> Just (negate x)))

kleisliMaybeLeft, kleisliMaybeRight :: (Kleisli Maybe Int Int, Kleisli Maybe Int Int)
kleisliMaybeLeft = (Kleisli (\x -> Just (x + 1)), Kleisli (\x -> if even x then Just (x * 2) else Nothing))
kleisliMaybeRight = (Kleisli (\x -> Just (x - 3)), Kleisli (\x -> Just (negate x)))

-- | 'gbifunctorLaws' for one category at all three tensors. @run@ is rank-2 so
-- the single observer serves every tensor. The endo-arrow pair is reused across
-- tensors since every factor is 'Int'.
gbimapEveryTensor ::
  forall cat obs.
  ( GBifunctor cat cat cat (,),
    GBifunctor cat cat cat Either,
    GBifunctor cat cat cat These,
    Eq (obs (Int, Int)),
    Show (obs (Int, Int)),
    Eq (obs (Either Int Int)),
    Show (obs (Either Int Int)),
    Eq (obs (These Int Int)),
    Show (obs (These Int Int))
  ) =>
  String ->
  (forall z. cat z z -> z -> obs z) ->
  (cat Int Int, cat Int Int) ->
  (cat Int Int, cat Int Int) ->
  [(PropertyName, Property)]
gbimapEveryTensor lbl run l r =
  labeled (lbl <> " (,)") (gbifunctorLaws run l r genPairInt)
    <> labeled (lbl <> " Either") (gbifunctorLaws run l r genEitherInt)
    <> labeled (lbl <> " These") (gbifunctorLaws run l r genTheseInt)

--------------------------------------------------------------------------------

tests :: IO Bool
tests = do
  gbifunctor <-
    checkSequential $
      Group "GBifunctor laws" $
        concat
          [ gbimapEveryTensor "(->)" runFun funLeft funRight,
            gbimapEveryTensor "Op" runOp opLeft opRight,
            gbimapEveryTensor "Iso (->)" runIso isoLeft isoRight,
            labeled "Star Maybe These" (gbifunctorLaws runStarMaybe starMaybeLeft starMaybeRight genTheseInt),
            labeled "Kleisli Maybe These" (gbifunctorLaws runKleisliMaybe kleisliMaybeLeft kleisliMaybeRight genTheseInt)
          ]
  iso <-
    checkSequential $
      Group "Iso laws" $
        concat
          [ labeled "(->) succ/pred" (isoLaws runFun (Iso (+ 1) (subtract 1) :: Iso (->) Int Int) genInt genInt),
            labeled "(->) not/not" (isoLaws runFun (Iso not not :: Iso (->) Bool Bool) genBool genBool)
          ]
  associative <-
    checkSequential $
      Group "Associative laws" $
        concat
          [ labeled "(->) (,)" (associativeLaws runFun genTPair),
            labeled "(->) Either" (associativeLaws runFun genTEither),
            labeled "(->) These" (associativeLaws runFun genTThese),
            labeled "Op (,)" (associativeLaws runOp genTPair),
            labeled "Op Either" (associativeLaws runOp genTEither),
            labeled "Op These" (associativeLaws runOp genTThese),
            labeled "Star Maybe These" (associativeLaws runStarMaybe genTThese),
            labeled "Kleisli Maybe These" (associativeLaws runKleisliMaybe genTThese)
          ]
  tensor <-
    checkSequential $
      Group "Tensor laws" $
        concat
          [ labeled "(->) (,) ()" (tensorLaws runFun (genTPair (pure ()) genInt) (genTPair genInt (pure ()))),
            labeled "(->) Either Void" (tensorLaws runFun (Right <$> genInt :: Gen (Either Void Int)) (Left <$> genInt :: Gen (Either Int Void))),
            labeled "(->) These Void" (tensorLaws runFun (That <$> genInt :: Gen (These Void Int)) (This <$> genInt :: Gen (These Int Void))),
            labeled "Op (,) ()" (tensorLaws runOp (genTPair (pure ()) genInt) (genTPair genInt (pure ()))),
            labeled "Op Either Void" (tensorLaws runOp (Right <$> genInt :: Gen (Either Void Int)) (Left <$> genInt :: Gen (Either Int Void))),
            labeled "Op These Void" (tensorLaws runOp (That <$> genInt :: Gen (These Void Int)) (This <$> genInt :: Gen (These Int Void))),
            labeled "Star Maybe These Void" (tensorLaws runStarMaybe (That <$> genInt :: Gen (These Void Int)) (This <$> genInt :: Gen (These Int Void))),
            labeled "Kleisli Maybe These Void" (tensorLaws runKleisliMaybe (That <$> genInt :: Gen (These Void Int)) (This <$> genInt :: Gen (These Int Void)))
          ]
  symmetric <-
    checkSequential $
      Group "Symmetric laws" $
        concat
          [ labeled "(->) (,)" (symmetricLaws runFun genTPair),
            labeled "(->) Either" (symmetricLaws runFun genTEither),
            labeled "(->) These" (symmetricLaws runFun genTThese),
            labeled "Op (,)" (symmetricLaws runOp genTPair),
            labeled "Op Either" (symmetricLaws runOp genTEither),
            labeled "Op These" (symmetricLaws runOp genTThese),
            labeled "Star Maybe These" (symmetricLaws runStarMaybe genTThese),
            labeled "Kleisli Maybe These" (symmetricLaws runKleisliMaybe genTThese)
          ]
  pure (and [gbifunctor, iso, associative, tensor, symmetric])
