module Data.Bifunctor.Module where

--------------------------------------------------------------------------------
-- LeftModule

class LeftModule cat t1 t2 f where
  lstrength :: cat (f a b) (f (t1 a x) (t2 b x))

-- Strong is LeftModule (->) (,) (,)

--------------------------------------------------------------------------------
-- RightModule

class RightModule cat t1 t2 f where
  rstrength :: cat (f a b) (f (x `t1` a) (x `t2` b))
 
--------------------------------------------------------------------------------
-- Bimmodule

class (LeftModule cat t1 t2 f, RightModule cat t1 t2 f) => Bimodule cat t1 t2 f
