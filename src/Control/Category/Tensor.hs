{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Control.Category.Tensor
  ( -- * Iso
    Iso (..),

    -- * Associative
    Associative (..),

    -- * Tensor
    Tensor (..),

    -- * Symmetric
    Symmetric (..),
  )
where

--------------------------------------------------------------------------------

import Control.Applicative (Applicative (..))
import Control.Arrow (Kleisli (..))
import Control.Category (Category (..))
import Data.Biapplicative (Biapplicative (..))
import Data.Functor.Contravariant (Op (..))
import Data.Profunctor (Profunctor (..), Star (..))
import Data.These (These (..), these)
import Data.Void (Void, absurd)
import Prelude hiding (Applicative (..), id, (.))
import qualified Kindly
import Kindly (type (~>))

--------------------------------------------------------------------------------

-- | An invertible mapping between 'a' and 'b' in category 'cat'.
--
-- === Laws
--
-- @
-- 'fwd' '.' 'bwd' ≡ 'id'
-- 'bwd' '.' 'fwd' ≡ 'id'
-- @
data Iso cat a b = Iso {fwd :: cat a b, bwd :: cat b a}

instance (Category cat) => Category (Iso cat) where
  id :: Iso cat a a
  id = Iso id id

  (.) :: Iso cat b c -> Iso cat a b -> Iso cat a c
  bc . ab = Iso (fwd bc . fwd ab) (bwd ab . bwd bc)

--------------------------------------------------------------------------------

-- | A bifunctor \(\_\otimes\_: \mathcal{C} \times \mathcal{C} \to \mathcal{C}\) is
-- 'Associative' if it is equipped with a
-- <https://ncatlab.org/nlab/show/natural+isomorphism natural isomorphism> of the form
-- \(\alpha_{x,y,z} : (x \otimes (y \otimes z)) \to ((x \otimes y) \otimes z)\), which
-- we call 'assoc'.
--
-- === Laws
--
-- @
-- 'fwd' 'assoc' '.' 'bwd' 'assoc' ≡ 'id'
-- 'bwd' 'assoc' '.' 'fwd' 'assoc' ≡ 'id'
-- @
class (Category cat, Kindly.FunctorOf cat (cat ~> cat) t) => Associative cat t where
  -- | The <https://ncatlab.org/nlab/show/natural+isomorphism natural isomorphism> between left and
  -- right associated nestings of @t@.
  --
  -- ==== __Examples__
  --
  -- >>> :t assoc @(->) @(,)
  -- assoc @(->) @(,) :: Iso (->) (a, (b, c)) ((a, b), c)
  --
  -- >>> fwd (assoc @(->) @(,)) (1, ("hello", True))
  -- ((1,"hello"),True)
  assoc :: Iso cat (a `t` (b `t` c)) ((a `t` b) `t` c)

instance (Associative (->) t) => Associative Op t where
  assoc :: Iso Op (a `t` (b `t` c)) ((a `t` b) `t` c)
  assoc =
    Iso
      { fwd = _, -- Op $ bwd assoc,
        bwd = _ -- Op $ fwd assoc
      }

instance Associative (->) (,) where
  assoc :: Iso (->) (a, (b, c)) ((a, b), c)
  assoc =
    Iso
      { fwd = \(a, (b, c)) -> ((a, b), c),
        bwd = \((a, b), c) -> (a, (b, c))
      }

instance Associative (->) Either where
  assoc :: Iso (->) (Either a (Either b c)) (Either (Either a b) c)
  assoc =
    Iso
      { fwd = either (Left . Left) (either (Left . Right) Right),
        bwd = either (fmap Left) (Right . Right)
      }

instance Associative (->) These where
  assoc :: Iso (->) (These a (These b c)) (These (These a b) c)
  assoc =
    Iso
      { fwd = these (This . This) (glmap That) (glmap . These),
        bwd = these (grmap This) (That . That) (flip $ grmap . flip These)
      }

instance (Monad m, Associative (->) t, Kindly.Bifunctor (Star m) (Star m) t) => Associative (Star m) t where
  assoc :: Iso (Star m) (a `t` (b `t` c)) ((a `t` b) `t` c)
  assoc =
    Iso
      { fwd = (`rmap` id) (fwd assoc),
        bwd = (`rmap` id) (bwd assoc)
      }

instance (Monad m, Associative (->) t, Kindly.Bifunctor (Kleisli m) (Kleisli m) t) => Associative (Kleisli m) t where
  assoc :: Iso (Kleisli m) (a `t` (b `t` c)) ((a `t` b) `t` c)
  assoc =
    Iso
      { fwd = (`rmap` id) (fwd assoc),
        bwd = (`rmap` id) (bwd assoc)
      }

--------------------------------------------------------------------------------

-- | A bifunctor \(\_ \otimes\_ \ : \mathcal{C} \times \mathcal{C} \to \mathcal{C}\)
-- that maps out of the <https://ncatlab.org/nlab/show/product+category product category> \(\mathcal{C} \times \mathcal{C}\)
-- is a 'Tensor' if it has:
--
-- 1. a corresponding identity type \(I\)
-- 2. Left and right <https://ncatlab.org/nlab/show/unitor#in_monoidal_categories unitor>
-- operations \(\lambda_{x} : 1 \otimes x \to x\) and \(\rho_{x} : x \otimes 1 \to x\), which we call 'unitr' and 'unitl'.
--
-- === Laws
--
-- @
-- 'fwd' 'unitr' (a ⊗ i) ≡ a
-- 'bwd' 'unitr' a ≡ (a ⊗ i)
--
-- 'fwd' 'unitl' (i ⊗ a) ≡ a
-- 'bwd' 'unitl' a ≡ (i ⊗ a)
-- @
class (Associative cat t) => Tensor cat t i | t -> i where
  -- | The <https://ncatlab.org/nlab/show/natural+isomorphism natural isomorphism> between @(i \`t\` a)@ and @a@.
  --
  -- ==== __Examples__
  --
  -- >>> fwd (unitl @_ @(,)) ((), True)
  -- True
  --
  -- >>> bwd (unitl @_ @(,)) True
  -- ((),True)
  --
  -- >>> bwd (unitl @_ @Either) True
  -- Right True
  --
  -- >>> :t bwd (unitl @_ @Either) True
  -- bwd (unitl @_ @Either) True :: Either Void Bool
  unitl :: Iso cat (i `t` a) a

  -- | The <https://ncatlab.org/nlab/show/natural+isomorphism natural isomorphism> between @(a \`t\` i)@ and @a@.
  --
  -- ==== __Examples__
  --
  -- >>> fwd (unitr @_ @(,)) (True, ())
  -- True
  --
  -- >>> bwd (unitr @_ @(,)) True
  -- (True,())
  --
  -- >>> bwd (unitr @_ @Either) True
  -- Left True
  --
  -- >>> :t bwd (unitr @_ @Either) True
  -- bwd (unitr @_ @Either) True :: Either Bool Void
  unitr :: Iso cat (a `t` i) a

instance (Tensor (->) t i) => Tensor Op t i where
  unitl :: Iso Op (i `t` a) a
  unitl =
    Iso
      { fwd = Op $ bwd unitl,
        bwd = Op $ fwd unitl
      }

  unitr :: Iso Op (a `t` i) a
  unitr =
    Iso
      { fwd = Op $ bwd unitr,
        bwd = Op $ fwd unitr
      }

instance Tensor (->) (,) () where
  unitl :: Iso (->) ((), a) a
  unitl =
    Iso
      { fwd = snd,
        bwd = bipure ()
      }

  unitr :: Iso (->) (a, ()) a
  unitr =
    Iso
      { fwd = fst,
        bwd = (`bipure` ())
      }

instance Tensor (->) Either Void where
  unitl :: Iso (->) (Either Void a) a
  unitl =
    Iso
      { fwd = either absurd id,
        bwd = pure
      }

  unitr :: Iso (->) (Either a Void) a
  unitr =
    Iso
      { fwd = either id absurd,
        bwd = Left
      }

instance Tensor (->) These Void where
  unitl :: Iso (->) (These Void a) a
  unitl =
    Iso
      { fwd = these absurd id (\_ x -> x),
        bwd = That
      }

  unitr :: Iso (->) (These a Void) a
  unitr =
    Iso
      { fwd = these id absurd const,
        bwd = This
      }

instance (Monad m, Tensor (->) t i, Associative (Star m) t) => Tensor (Star m) t i where
  unitl :: Iso (Star m) (i `t` a) a
  unitl =
    Iso
      { fwd = (`rmap` id) (fwd unitl),
        bwd = (`rmap` id) (bwd unitl)
      }

  unitr :: Iso (Star m) (a `t` i) a
  unitr =
    Iso
      { fwd = (`rmap` id) (fwd unitr),
        bwd = (`rmap` id) (bwd unitr)
      }

instance (Monad m, Tensor (->) t i, Associative (Kleisli m) t) => Tensor (Kleisli m) t i where
  unitl :: Iso (Kleisli m) (i `t` a) a
  unitl =
    Iso
      { fwd = (`rmap` id) (fwd unitl),
        bwd = (`rmap` id) (bwd unitl)
      }

  unitr :: Iso (Kleisli m) (a `t` i) a
  unitr =
    Iso
      { fwd = (`rmap` id) (fwd unitr),
        bwd = (`rmap` id) (bwd unitr)
      }

--------------------------------------------------------------------------------

-- | A bifunctor \(\_ \otimes\_ \ : \mathcal{C} \times \mathcal{C} \to \mathcal{C}\)
-- is 'Symmetric' if it has a product operation \(B_{x,y} : x \otimes y \to y \otimes x\)
-- such that \(B_{x,y} \circ B_{x,y} \equiv 1_{x \otimes y}\), which we call 'swap'.
--
-- === Laws
--
-- @
-- 'swap' '.' 'swap' ≡ 'id'
-- @
class (Associative cat t) => Symmetric cat t where
  -- | @swap@ is a symmetry isomorphism for @t@
  --
  -- ==== __Examples__
  --
  -- >>> :t swap @(->) @(,)
  -- swap @(->) @(,) :: (a, b) -> (b, a)
  --
  -- >>> swap @(->) @(,) (True, "hello")
  -- ("hello",True)
  --
  -- >>> :t swap @(->) @Either (Left True)
  -- swap @(->) @Either (Left True) :: Either b Bool
  --
  -- >>> swap @(->) @Either (Left True)
  -- Right True
  swap :: cat (a `t` b) (b `t` a)

instance (Symmetric (->) t) => Symmetric Op t where
  swap :: Op (a `t` b) (b `t` a)
  swap = Op swap

instance Symmetric (->) (,) where
  swap :: (a, b) -> (b, a)
  swap (a, b) = (b, a)

instance Symmetric (->) Either where
  swap :: Either a b -> Either b a
  swap = either Right Left

instance Symmetric (->) These where
  swap :: These a b -> These b a
  swap = these That This (flip These)

instance (Monad m, Symmetric (->) t, Associative (Star m) t) => Symmetric (Star m) t where
  swap :: Star m (a `t` b) (b `t` a)
  swap = Star $ pure . swap

instance (Monad m, Symmetric (->) t, Associative (Kleisli m) t) => Symmetric (Kleisli m) t where
  swap :: Kleisli m (a `t` b) (b `t` a)
  swap = Kleisli $ pure . swap
