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

class LeftModule cat t1 t2 t3 f where
  lstrength :: cat (f a b c) (f (t1 a x) (t2 b x) (t3 c x))

--------------------------------------------------------------------------------

class RightModule cat t1 t2 t3 f where
  rstrength :: cat (f a b c) (f (t1 x a) (t2 x b) (t3 x c))

--------------------------------------------------------------------------------

class (LeftModule cat t1 t2 t3 f, RightModule cat t1 t2 t3 f) => Bimodule cat t1 t2 t3 f
