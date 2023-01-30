{-# LANGUAGE DefaultSignatures #-}
module Data.Functor.Invariant
  ( -- * Invariant
    Invariant (..),
    invIso,
  )
where

--------------------------------------------------------------------------------

import Control.Applicative (ZipList)
import Control.Category.Tensor (Iso (Iso))
import Data.Functor.Compose (Compose (..))
import Data.Functor.Contravariant (Contravariant (..))
import Data.Functor.Identity (Identity (Identity))
import Data.Functor.Product (Product)
import Data.Functor.Sum (Sum)
import Data.List.NonEmpty (NonEmpty)
import Prelude

--------------------------------------------------------------------------------

-- | A functor is 'Invariant' if it is parametric in its type
-- parameter @a@.
--
-- === Laws
--
-- @
-- 'invmap' 'id' 'id' ≡ 'id'
-- 'invmap' @f2@ @f2'@ 'Control.Category..' 'invmap' @f1@ @f1'@ ≡ 'invmap' (@f2@ 'Control.Category..' @f1@) (@f1'@ 'Control.Category..' @f2'@)
-- @
class Invariant f where
  -- | Given two isomorphic functions @f@ and @g@, map over the
  -- invariant parameter @a@.
  --
  -- ==== __Examples__
  --
  -- >>> :t invmap @Identity (read @Bool) show
  -- invmap @Identity (read @Bool) show :: Identity String -> Identity Bool
  --
  -- >>> invmap @Identity (read @Bool) show (Identity "True")
  -- Identity True
  invmap :: (a -> a') -> (a' -> a) -> f a -> f a'
  default invmap :: Functor f => (a -> a') -> (a' -> a) -> f a -> f a'
  invmap = invmapFunctor

invIso :: Invariant f => Iso (->) a a' -> Iso (->) (f a) (f a')
invIso (Iso f g)  = Iso (invmap f g) (invmap g f)

newtype FromFunctor f a = FromFunctor { runBi :: f a }

-- | Every 'Functor' is also an 'Invariant' functor.
invmapFunctor :: Functor f => (a -> b) -> (b -> a) -> f a -> f b
invmapFunctor = flip $ const fmap

instance Functor f => Invariant (FromFunctor f) where
  invmap :: (a -> a') -> (a' -> a) -> FromFunctor f a -> FromFunctor f a'
  invmap f _ = FromFunctor . fmap f . runBi

newtype FromContra f a = FromContra { runContra :: f a }

instance Contravariant f => Invariant (FromContra f) where
  invmap :: (a -> a') -> (a' -> a) -> FromContra f a -> FromContra f a'
  invmap _ g = FromContra . contramap g . runContra

deriving via FromFunctor Identity           instance Invariant Identity
deriving via FromFunctor (Compose f g)      instance (Functor f, Functor g) => Invariant (Compose f g)
deriving via FromFunctor []                 instance Invariant []
deriving via FromFunctor ZipList            instance Invariant ZipList
deriving via FromFunctor NonEmpty           instance Invariant NonEmpty
deriving via FromFunctor Maybe              instance Invariant Maybe
deriving via FromFunctor (Either e)         instance Invariant (Either e)
deriving via FromFunctor IO                 instance Invariant IO
deriving via FromFunctor (Sum f g)          instance (Functor f, Functor g) => Invariant (Sum f g)
deriving via FromFunctor (Product f g)      instance (Functor f, Functor g) => Invariant (Product f g)
deriving via (FromFunctor ((,) x1))         instance Invariant ((,) x1)
deriving via (FromFunctor ((,,) x1 x2))     instance Invariant ((,,) x1 x2)
deriving via (FromFunctor ((,,,) x1 x2 x3)) instance Invariant ((,,,) x1 x2 x3)
