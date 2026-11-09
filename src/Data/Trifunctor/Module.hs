module Data.Trifunctor.Module
  ( -- * LeftModule
    LeftModule (..),

    -- * RightModule
    RightModule (..),

    -- * Bimodule
    Bimodule,
  )
where

--------------------------------------------------------------------------------

class LeftModule cat tC1 tC2 tC3 f where
  lstrength :: cat (f a b c) (f (tC1 a x) (tC2 b x) (tC3 c x))

--------------------------------------------------------------------------------

class RightModule cat tC1 tC2 tC3 f where
  rstrength :: cat (f a b c) (f (tC1 x a) (tC2 x b) (tC3 x c))

--------------------------------------------------------------------------------

class (LeftModule cat tC1 tC2 tC3 f, RightModule cat tC1 tC2 tC3 f) => Bimodule cat tC1 tC2 tC3 f
