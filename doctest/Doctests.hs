{-# LANGUAGE CPP #-}

module Main (main) where

import Prelude
import Data.Maybe (isJust)
import System.Environment (getArgs, lookupEnv)
import Test.DocTest (mainFromCabal)

-- doctest-parallel builds its GHC invocation from the .cabal file alone, so its
-- parsing pass does not expose the library's dependencies. GHC still auto-defines
-- the CPP version macros for always-available packages such as base, but not for
-- semialign, so the modules that guard imports on MIN_VERSION_semialign fail to
-- preprocess. We reconstruct that macro from the version Cabal resolved for
-- this test-suite and hand it to doctest's parsing GHC via --ghc-arg. Deriving it
-- from the resolved version keeps it correct across the CI GHC matrix.
ghcArgs :: [String]
ghcArgs =
  -- doctest-parallel does not inherit the library's ghc-options, so re-add the two
  -- that only affect warning noise while parsing sources: -Wno-star-is-type matches
  -- the library (several modules use `*` in kind signatures), and -optP-w silences
  -- the harmless "macro redefined" note from the semialign macro below.
  [ "--ghc-arg=-Wno-star-is-type"
  , "--ghc-arg=-optP-w"
  , "--ghc-arg=" ++ minVersionMacro "semialign" VERSION_semialign
  ]

-- | Build a Cabal-style @MIN_VERSION_<pkg>(a,b,c)@ preprocessor definition for a
-- concrete version string, e.g. @"1.4"@ yields a body that is true exactly when
-- @(a,b,c) <= 1.4.0@.
minVersionMacro :: String -> String -> String
minVersionMacro pkg version =
  "-optP-DMIN_VERSION_" ++ pkg ++ "(a,b,c)=" ++ body
  where
    (a, b, c) = case versionParts version of
      (x : y : z : _) -> (x, y, z)
      [x, y] -> (x, y, 0)
      [x] -> (x, 0, 0)
      [] -> (0, 0, 0)
    body =
      "((a)<" ++ show a
        ++ "||((a)==" ++ show a ++ "&&(b)<" ++ show b ++ ")"
        ++ "||((a)==" ++ show a ++ "&&(b)==" ++ show b ++ "&&(c)<=" ++ show c ++ "))"

versionParts :: String -> [Int]
versionParts = map read . splitOnDot
  where
    splitOnDot s = case break (== '.') s of
      (chunk, []) -> [chunk]
      (chunk, _ : rest) -> chunk : splitOnDot rest

main :: IO ()
main = do
  args <- getArgs
  -- Inside a `nix develop` shell we still build with cabal-install, so the
  -- cabal-generated GHC environment file is what exposes the package and its
  -- dependencies. doctest-parallel otherwise reads IN_NIX_SHELL as "packages come
  -- from Nix" and disables that file with `-package-env -`, which hides every
  -- dependency. Opt out of its Nix mode here. A real `nix build` sets
  -- NIX_BUILD_TOP instead and keeps doctest-parallel's Nix handling.
  inNixShell <- isJust <$> lookupEnv "IN_NIX_SHELL"
  let nixArgs = ["--no-nix" | inNixShell]
  mainFromCabal "monoidal-functors" (ghcArgs ++ nixArgs ++ args)
