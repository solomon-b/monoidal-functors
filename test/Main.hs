module Main where

import Prelude
import Test.DocTest ( doctest )
import System.Process

main :: IO ()
main = do
  let cmd = shell "find src -name '*.hs'"
  hsString <- readCreateProcess cmd ""
  let sources = lines hsString
  print sources
  doctest
    $ "-isrc"
    : "-XConstraintKinds"
    : "-XDeriveFunctor"
    : "-XDerivingVia"
    : "-XFunctionalDependencies"
    : "-XFlexibleInstances"
    : "-XFlexibleContexts"
    : "-XGeneralizedNewtypeDeriving"
    : "-XImportQualifiedPost"
    : "-XInstanceSigs"
    : "-XKindSignatures"
    : "-XLambdaCase"
    : "-XMultiParamTypeClasses"
    : "-XNoImplicitPrelude"
    : "-XQuantifiedConstraints"
    : "-XRankNTypes"
    : "-XScopedTypeVariables"
    : "-XStandaloneDeriving"
    : "-XTupleSections"
    : "-XTypeApplications"
    : "-XTypeOperators"
    : "-XUndecidableInstances"
    : "-XDataKinds"
    : sources


