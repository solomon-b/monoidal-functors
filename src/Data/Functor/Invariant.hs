module Data.Functor.Invariant where

import Prelude
import Control.Applicative (ZipList)
import Control.Category.Tensor
import Data.Functor.Contravariant
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Sum
import Data.Functor.Product
import Data.List.NonEmpty (NonEmpty)

class Invariant f where
  invmap :: (a -> a') -> (a' -> a) -> f a -> f a'

invIso :: Invariant f => Iso (->) a a' -> Iso (->) (f a) (f a')
invIso (Iso f g)  = Iso (invmap f g) (invmap g f)

newtype FromFunctor f a = FromFunctor { runBi :: f a }

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
