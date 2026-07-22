-- | Test driver. Runs the generic-deriving suite and the laws sublibrary
-- self-test, and fails if either does.
module Main (main) where

import Control.Monad (unless)
import Data.Functor.Monoidal.GenericSpec qualified as GenericSpec
import Data.Functor.Monoidal.LawsSpec qualified as LawsSpec
import System.Exit (exitFailure)
import Prelude

--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== generic deriving ==="
  generic <- GenericSpec.tests
  putStrLn "=== laws sublibrary self-test ==="
  laws <- LawsSpec.tests
  unless (generic && laws) exitFailure
