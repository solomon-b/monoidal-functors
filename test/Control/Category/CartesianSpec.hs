{-# LANGUAGE OverloadedStrings #-}

-- | Self-test: run the exported "Control.Category.Cartesian.Laws" 'Laws' against
-- the instances the library ships for 'Semicartesian', 'Semicocartesian',
-- 'Cartesian', and 'Cocartesian'.
--
-- The diagonal/codiagonal coassociativity laws are non-endomorphic, so they are
-- observed forward at @('->')@ only. The projection/inclusion unit laws are
-- endomorphic, so they are additionally checked at 'Op' (whose 'Cartesian' /
-- 'Cocartesian' instances are the duals of the @('->')@ ones).
module Control.Category.CartesianSpec (tests) where

--------------------------------------------------------------------------------

import Control.Category.Cartesian.Laws
  ( cartesianLaws,
    cocartesianLaws,
    semicartesianLaws,
    semicocartesianLaws,
  )
import Control.Category.LawsSupport (genTEither, labeled, runFun, runOp)
import Data.Functor.Contravariant (Op)
import Data.Void (Void)
import Hedgehog (Group (..), checkSequential)
import Prelude

--------------------------------------------------------------------------------

tests :: IO Bool
tests = do
  semicartesian <-
    checkSequential $
      Group "Semicartesian laws" $
        labeled "(->) (,)" (semicartesianLaws @(->) @(,) runFun)
  semicocartesian <-
    checkSequential $
      Group "Semicocartesian laws" $
        labeled "(->) Either" (semicocartesianLaws @(->) @Either runFun genTEither)
  cartesian <-
    checkSequential $
      Group "Cartesian laws" $
        concat
          [ labeled "(->) (,) ()" (cartesianLaws @(->) @(,) @() runFun),
            labeled "Op Either Void" (cartesianLaws @Op @Either @Void runOp)
          ]
  cocartesian <-
    checkSequential $
      Group "Cocartesian laws" $
        concat
          [ labeled "(->) Either Void" (cocartesianLaws @(->) @Either @Void runFun),
            labeled "Op (,) ()" (cocartesianLaws @Op @(,) @() runOp)
          ]
  pure (and [semicartesian, semicocartesian, cartesian, cocartesian])
