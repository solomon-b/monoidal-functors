module Control.Category.Cartesian
  ( -- * Semicartesian
    Semicartesian (..),
    (/\),

    -- * Semicocartesian
    Semicocartesian (..),
    (\/),

    -- * Cartesian
    Cartesian (..),

    -- * Cocartesian
    Cocartesian (..)

  )
where

--------------------------------------------------------------------------------

import Control.Category (id, (>>>))
import Control.Category.Tensor
import Data.Functor.Contravariant (Op (..))
import Data.Void (Void, absurd)
import Prelude hiding (id)

--------------------------------------------------------------------------------

-- | A 'Category' is 'Semicartesian' if it is equipped with a
-- 'Symmetric' type operator @t@ and each object comes equipped with a
-- morphism @a \`cat\` (a \`t\` a)@.
--
-- === Laws
--
-- @
-- grmap split ∘ split ≡ fwd assoc ∘ glmap split ∘ split
-- glmap split ∘ split ≡ bwd assoc ∘ grmap split ∘ split
-- @
class Symmetric cat t => Semicartesian cat t where
  -- | TODO
  --
  -- ==== __Examples__
  --
  -- >>> split @(->) @(,) True
  -- (True,True)
  split :: cat a (a `t` a)

  -- | TODO
  --
  -- ==== __Examples__
  --
  -- >>> :t fork @(->) @(,) show not 
  -- fork @(->) @(,) show not :: Bool -> (String, Bool)
  --
  -- >>> fork @(->) @(,) show not True
  -- ("True",False)
  fork :: cat a x -> cat a y -> cat a (x `t` y)
  fork f g = split >>> f # g

  {-# MINIMAL split #-}

-- | Infix version of 'fork'.
infixr 9 /\
(/\) :: Semicartesian cat t =>  cat a x -> cat a y -> cat a (x `t` y)
(/\) = fork

instance Semicartesian (->) (,) where
  split :: a -> (a, a)
  split    a =  (a, a)

instance Semicocartesian (->) t => Semicartesian Op t where
  split = Op merge

--------------------------------------------------------------------------------

-- | A 'Category' is 'Semicocartesian' if it is equipped with a
-- 'Symmetric' binary operator and each object comes equipped with a
-- morphism @a \`cat\` (a \`t\` a)@.
--
-- === Laws
--
-- @
-- TODO
-- @
class Symmetric cat t => Semicocartesian cat t where
  -- | TODO
  --
  -- ==== __Examples__
  --
  -- >>> :t merge @(->) @(Either) (Left True)
  -- merge @(->) @(Either) (Left True) :: Bool
  --
  -- >>> merge @(->) @(Either) (Left True)
  -- True
  merge :: cat (a `t` a) a

  -- | TODO
  --
  -- ==== __Examples__
  --
  fuse :: cat x a -> cat y a -> cat (x `t` y) a
  fuse f g = f # g >>> merge

  {-# MINIMAL merge #-}

-- | Infix version of 'fuse'.
infixr 9 \/
(\/) :: Semicocartesian cat t => cat x a -> cat y a -> cat (x `t` y) a
(\/) = fuse

instance Semicocartesian (->) Either where
  merge :: Either a a -> a
  merge =  either id id

instance Semicartesian (->) t => Semicocartesian Op t where
  merge = Op split

--------------------------------------------------------------------------------
-- Cartesian

-- | A 'Category' equipped with a 'Tensor' @t@ where every object @a@
-- is equipped with a morphism to the 'Tensor' unit @i@.
--
-- === Laws
--
-- @
-- TODO
-- @
class (Semicartesian cat t, Tensor cat t i) => Cartesian cat t i | i -> t, t -> i where
  -- | TODO
  --
  -- ==== __Examples__
  --
  -- >>> kill @(->) @(,) @() True
  -- ()
  kill :: cat a i

  -- | TODO
  --
  -- ==== __Examples__
  --
  -- >>> projl @(->) @(,) (True, "hello")
  -- True
  projl :: cat (x `t` y) x
  projl = id # kill >>> fwd unitr

  -- | TODO
  --
  -- ==== __Examples__
  --
  -- >>> projr @(->) @(,) (True, "hello")
  -- "hello"
  projr :: cat (x `t` y) y
  projr = kill # id >>> fwd unitl

  -- | TODO
  --
  -- ==== __Examples__
  --
  unfork :: cat a (x `t` y) -> (cat a x, cat a y)
  unfork h = (h >>> projl, h >>> projr)

  {-# MINIMAL kill #-}

instance Cartesian (->) (,) () where
  kill :: a -> ()
  kill = const ()

instance Cocartesian (->) t i => Cartesian Op t i where
  kill = Op spawn

--------------------------------------------------------------------------------
-- Cocartesian

-- | A 'Category' equipped with a 'Tensor' @t@ where every object @a@
-- is equipped with a morphism from the 'Tensor' unit @i@.
--
-- === Laws
--
-- @
-- TODO
-- @
class (Semicocartesian cat t, Tensor cat t i) => Cocartesian cat t i | i -> t, t -> i where
  -- | TODO
  --
  -- ==== __Examples__
  --
  spawn :: cat i a

  -- | TODO
  --
  -- ==== __Examples__
  --
  incll :: cat x (x `t` y)
  incll = bwd unitr >>> id # spawn

  -- | TODO
  --
  -- ==== __Examples__
  --
  inclr :: cat y (x `t` y)
  inclr = bwd unitl >>> spawn # id

  -- | TODO
  --
  -- ==== __Examples__
  --
  unfuse :: cat (x `t` y) a -> (cat x a, cat y a)
  unfuse h = (incll >>> h, inclr >>> h)

  {-# MINIMAL spawn #-}

instance Cartesian (->) t i => Cocartesian Op t i where
  spawn = Op kill

instance Cocartesian (->) Either Void where
  spawn :: Void -> a
  spawn = absurd
