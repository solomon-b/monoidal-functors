-- | Test driver. Runs the generic-deriving suite and the laws sublibrary
-- self-test, and fails if either does.
module Main (main) where

import Control.Category.CartesianSpec qualified as CartesianSpec
import Control.Category.TensorSpec qualified as TensorSpec
import Control.Monad (unless)
import Data.Functor.Monoidal.GenericSpec qualified as GenericSpec
import Data.Functor.Monoidal.LawsSpec qualified as LawsSpec
import System.Exit (exitFailure)
import Prelude

--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "=== Control.Category.Tensor laws ==="
  tensor <- TensorSpec.tests
  putStrLn "=== Control.Category.Cartesian laws ==="
  cartesian <- CartesianSpec.tests
  putStrLn "=== generic deriving ==="
  generic <- GenericSpec.tests
  putStrLn "=== laws sublibrary self-test ==="
  laws <- LawsSpec.tests
  unless (tensor && cartesian && generic && laws) exitFailure
