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
    Cocartesian (..),
  )
where

--------------------------------------------------------------------------------

import Control.Category (id, (>>>))
import Control.Category.Tensor (Iso (..), Symmetric, Tensor (..), (#))
import Data.Functor.Contravariant (Op (..))
import Data.Void (Void, absurd)
import Prelude hiding (fst, id, snd)

--------------------------------------------------------------------------------

-- | A 'Category' is 'Semicartesian' if it is equipped with a
-- 'Symmetric' bifunctor @t@ and each object comes equipped with a
-- <https://ncatlab.org/nlab/show/diagonal+morphism diagonal morphism>
-- \(\Delta_x: x \to x \otimes x \), which we call 'split'.
--
-- === Laws
--
-- @
-- 'Control.Category.Tensor.grmap' 'split' '.' 'split' ≡ 'bwd' 'Control.Category.Tensor.assoc' '.' 'Control.Category.Tensor.glmap' 'split' '.' 'split'
-- 'Control.Category.Tensor.glmap' 'split' '.' 'split' ≡ 'fwd' 'Control.Category.Tensor.assoc' '.' 'Control.Category.Tensor.grmap' 'split' '.' 'split'
-- @
class Symmetric cat t => Semicartesian cat t where
  -- | The <https://ncatlab.org/nlab/show/diagonal+morphism diagonal morphism> of @a@ in @cat@. We can think of 'split'
  -- as duplicating data.
  --
  -- ==== __Examples__
  --
  -- >>> split @(->) @(,) True
  -- (True,True)
  split :: cat a (a `t` a)

  -- | Given morphisms @cat a x@ and @cat a y@, construct the
  -- universal map @cat a (x \`t\` y)@.
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

(/\) :: Semicartesian cat t => cat a x -> cat a y -> cat a (x `t` y)
(/\) = fork

instance Semicartesian (->) (,) where
  split :: a -> (a, a)
  split a = (a, a)

instance Semicocartesian (->) t => Semicartesian Op t where
  split :: Semicocartesian (->) t => Op a (t a a)
  split = Op merge

--------------------------------------------------------------------------------

-- | A 'Category' is 'Semicocartesian' if it is equipped with a
-- 'Symmetric' type operator @t@ and each object comes equipped with a
-- morphism \(\Delta^{-1}_x: x \otimes x \to x\), which we call 'merge'.
--
-- === Laws
--
-- @
-- 'merge' '.' 'Control.Category.Tensor.grmap' 'merge' ≡ 'merge' . 'Control.Category.Tensor.glmap' 'merge' '.' 'fwd' 'Control.Category.Tensor.assoc'
-- 'merge' '.' 'Control.Category.Tensor.glmap' 'merge' ≡ 'merge' . 'Control.Category.Tensor.grmap' 'merge' '.' 'bwd' 'Control.Category.Tensor.assoc'
-- @
class Symmetric cat t => Semicocartesian cat t where
  -- | The <https://ncatlab.org/nlab/show/codiagonal co-diagonal morphism> of @a@ in @cat@.
  --
  -- ==== __Examples__
  --
  -- >>> :t merge @(->) @(Either) (Left True)
  -- merge @(->) @(Either) (Left True) :: Bool
  --
  -- >>> merge @(->) @(Either) (Left True)
  -- True
  merge :: cat (a `t` a) a

  -- | Given morphisms @cat x a@ and @cat y a@, construct the
  -- universal map @cat (x \`t\` y) a@.
  --
  -- ==== __Examples__
  fuse :: cat x a -> cat y a -> cat (x `t` y) a
  fuse f g = f # g >>> merge

  {-# MINIMAL merge #-}

-- | Infix version of 'fuse'.
infixr 9 \/

(\/) :: Semicocartesian cat t => cat x a -> cat y a -> cat (x `t` y) a
(\/) = fuse

instance Semicocartesian (->) Either where
  merge :: Either a a -> a
  merge = either id id

instance Semicartesian (->) t => Semicocartesian Op t where
  merge :: Semicartesian (->) t => Op (t a a) a
  merge = Op split

--------------------------------------------------------------------------------

-- | A 'Category' equipped with a 'Tensor' @t@ where the 'Tensor' unit @i@ is the <https://ncatlab.org/nlab/show/terminal+object terminal object>
-- in @cat@ and thus every object @a@ is equipped with a morphism \(e_x: x \to I\), which we call 'kill'.
--
-- === Laws
--
-- @
-- 'fwd' 'unitl' '.' 'Control.Category.Tensor.glmap' 'kill' '.' 'split' ≡ 'id'
-- 'fwd' 'unitr' '.' 'Control.Category.Tensor.grmap' 'kill' '.' 'split' ≡ 'id'
-- @
class (Semicartesian cat t, Tensor cat t i) => Cartesian cat t i | i -> t, t -> i where
  -- | A morphism from the @a@ to the terminal object @i@ in @cat. We
  -- can think of 'kill' as deleting data where 'split' duplicates it.
  --
  -- ==== __Examples__
  --
  -- >>> kill @(->) @(,) @() True
  -- ()
  kill :: cat a i

  -- | The left projection for @t@.
  --
  -- ==== __Examples__
  --
  -- >>> projl @(->) @(,) (True, "hello")
  -- True
  projl :: cat (x `t` y) x
  projl = id # kill >>> fwd unitr

  -- | The right projection for @t@.
  --
  -- ==== __Examples__
  --
  -- >>> projr @(->) @(,) (True, "hello")
  -- "hello"
  projr :: cat (x `t` y) y
  projr = kill # id >>> fwd unitl

  -- | Given the universal map @cat a (x `t` y)@, construct morphisms @cat a x@ and @cat a y@.
  --
  -- ==== __Examples__
  unfork :: cat a (x `t` y) -> (cat a x, cat a y)
  unfork h = (h >>> projl, h >>> projr)

  {-# MINIMAL kill #-}

instance Cartesian (->) (,) () where
  kill :: a -> ()
  kill = const ()

instance Cocartesian (->) t i => Cartesian Op t i where
  kill :: Cocartesian (->) t i => Op a i
  kill = Op spawn

--------------------------------------------------------------------------------

-- | A 'Category' equipped with a 'Tensor' @t@ where the 'Tensor' unit @i@ is the <https://ncatlab.org/nlab/show/initial+object initial object>
-- in @cat@ and thus every object @a@ is equipped with a morphism \(e^{-1}_x: I \to x\), which we call 'spawn'.
--
-- === Laws
--
-- @
-- 'merge' '.' 'Control.Category.Tensor.glmap' 'spawn' '.' 'bwd' 'unitl' ≡ 'id'
-- 'merge' '.' 'Control.Category.Tensor.grmap' 'spawn' '.' 'bwd' 'unitr' ≡ 'id'
-- @
class (Semicocartesian cat t, Tensor cat t i) => Cocartesian cat t i | i -> t, t -> i where
  -- | A morphism from the initial object @i@ in @cat@ to @a@.
  --
  -- ==== __Examples__
  spawn :: cat i a

  -- | The left inclusion for @t@.
  --
  -- ==== __Examples__
  incll :: cat x (x `t` y)
  incll = bwd unitr >>> id # spawn

  -- | The right inclusion for @t@.
  --
  -- ==== __Examples__
  inclr :: cat y (x `t` y)
  inclr = bwd unitl >>> spawn # id

  -- | Given the universal map @cat (x `t` y) a@, construct morphisms @cat x a@ and @cat y a@.
  --
  -- ==== __Examples__
  unfuse :: cat (x `t` y) a -> (cat x a, cat y a)
  unfuse h = (incll >>> h, inclr >>> h)

  {-# MINIMAL spawn #-}

instance Cartesian (->) t i => Cocartesian Op t i where
  spawn :: Cartesian (->) t i => Op i a
  spawn = Op kill

instance Cocartesian (->) Either Void where
  spawn :: Void -> a
  spawn = absurd
