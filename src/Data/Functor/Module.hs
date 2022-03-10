module Data.Functor.Module where

import Data.Functor.Contravariant (Contravariant(..), Comparison, Equivalence, Predicate, Op)
import Data.Tuple (fst, snd)
import Data.Either (Either (..))
import Data.Functor (Functor (..))
import Data.Proxy (Proxy)
import GHC.Generics (U1, V1, Rec1, type (:+:), type (:*:), K1, type (:.:), M1)
import Data.Functor.Const (Const)
import Data.Monoid (Alt)
import Data.Functor.Product (Product)
import Data.Functor.Sum (Sum)
import Data.Functor.Compose (Compose)

newtype FromFunctor f a = FromFunctor (f a)
  deriving newtype (Functor)

newtype FromContra f a = FromContra (f a)
  deriving newtype (Contravariant)

-----------------------------------------------------------------------
-- LeftModule

class LeftModule cat t1 f where
  lstrength :: cat (f a) (f (t1 a x))

instance Contravariant f => LeftModule (->) (,) (FromContra f) where
  lstrength :: FromContra f a -> FromContra f (a, x)
  lstrength = contramap fst

deriving via (FromContra Comparison) instance LeftModule (->) (,) Comparison
deriving via (FromContra Equivalence) instance LeftModule (->) (,) Equivalence
deriving via (FromContra Predicate) instance LeftModule (->) (,) Predicate
deriving via (FromContra (Op a)) instance LeftModule (->) (,) (Op a)
deriving via (FromContra Proxy) instance LeftModule (->) (,) Proxy
deriving via (FromContra U1) instance LeftModule (->) (,) U1
deriving via (FromContra V1) instance LeftModule (->) (,) V1
deriving via (FromContra (Const a)) instance LeftModule (->) (,) (Const a)
deriving via (FromContra (Alt f)) instance Contravariant f => LeftModule (->) (,) (Alt f)
deriving via (FromContra (Rec1 f)) instance Contravariant f => LeftModule (->) (,) (Rec1 f)
deriving via (FromContra (Product f g)) instance (Contravariant f, Contravariant g) => LeftModule (->) (,) (Product f g)
deriving via (FromContra (Sum f g)) instance (Contravariant f, Contravariant g) => LeftModule (->) (,) (Sum f g)
deriving via (FromContra (f :+: g)) instance (Contravariant f, Contravariant g) => LeftModule (->) (,) (f :+: g)
deriving via (FromContra (f :*: g)) instance (Contravariant f, Contravariant g) => LeftModule (->) (,) (f :*: g)
deriving via (FromContra (K1 i c)) instance LeftModule (->) (,) (K1 i c)
deriving via (FromContra (Compose f g)) instance (Functor f, Contravariant g) => LeftModule (->) (,) (Compose f g)
deriving via (FromContra (f :.: g)) instance (Functor f, Contravariant g) => LeftModule (->) (,) (f :.: g)
deriving via (FromContra (M1 i c f)) instance Contravariant f => LeftModule (->) (,) (M1 i c f)

instance Functor f => LeftModule (->) Either (FromFunctor f) where
  lstrength :: FromFunctor f a -> FromFunctor f (Either a x)
  lstrength = fmap Left

instance Functor f => LeftModule (->) Either f where
  lstrength :: f a -> f (Either a x)
  lstrength = fmap Left

-----------------------------------------------------------------------
-- RightModule

class RightModule cat t1 f where
  rstrength :: cat (f a) (f (t1 x a))

instance Contravariant f => RightModule (->) (,) (FromContra f) where
  rstrength :: FromContra f a -> FromContra f (x, a)
  rstrength = contramap snd

deriving via (FromContra Comparison) instance RightModule (->) (,) Comparison
deriving via (FromContra Equivalence) instance RightModule (->) (,) Equivalence
deriving via (FromContra Predicate) instance RightModule (->) (,) Predicate
deriving via (FromContra (Op a)) instance RightModule (->) (,) (Op a)
deriving via (FromContra Proxy) instance RightModule (->) (,) Proxy
deriving via (FromContra U1) instance RightModule (->) (,) U1
deriving via (FromContra V1) instance RightModule (->) (,) V1
deriving via (FromContra (Const a)) instance RightModule (->) (,) (Const a)
deriving via (FromContra (Alt f)) instance Contravariant f => RightModule (->) (,) (Alt f)
deriving via (FromContra (Rec1 f)) instance Contravariant f => RightModule (->) (,) (Rec1 f)
deriving via (FromContra (Product f g)) instance (Contravariant f, Contravariant g) => RightModule (->) (,) (Product f g)
deriving via (FromContra (Sum f g)) instance (Contravariant f, Contravariant g) => RightModule (->) (,) (Sum f g)
deriving via (FromContra (f :+: g)) instance (Contravariant f, Contravariant g) => RightModule (->) (,) (f :+: g)
deriving via (FromContra (f :*: g)) instance (Contravariant f, Contravariant g) => RightModule (->) (,) (f :*: g)
deriving via (FromContra (K1 i c)) instance RightModule (->) (,) (K1 i c)
deriving via (FromContra (Compose f g)) instance (Functor f, Contravariant g) => RightModule (->) (,) (Compose f g)
deriving via (FromContra (f :.: g)) instance (Functor f, Contravariant g) => RightModule (->) (,) (f :.: g)
deriving via (FromContra (M1 i c f)) instance Contravariant f => RightModule (->) (,) (M1 i c f)

-----------------------------------------------------------------------
-- Bimodule

class (LeftModule cat t1 f, RightModule cat t1 f) => Bimodule cat t1 f

deriving via (FromContra Comparison) instance Bimodule (->) (,) Comparison
deriving via (FromContra Equivalence) instance Bimodule (->) (,) Equivalence
deriving via (FromContra Predicate) instance Bimodule (->) (,) Predicate
deriving via (FromContra (Op a)) instance Bimodule (->) (,) (Op a)
deriving via (FromContra Proxy) instance Bimodule (->) (,) Proxy
deriving via (FromContra U1) instance Bimodule (->) (,) U1
deriving via (FromContra V1) instance Bimodule (->) (,) V1
deriving via (FromContra (Const a)) instance Bimodule (->) (,) (Const a)
deriving via (FromContra (Alt f)) instance Contravariant f => Bimodule (->) (,) (Alt f)
deriving via (FromContra (Rec1 f)) instance Contravariant f => Bimodule (->) (,) (Rec1 f)
deriving via (FromContra (Product f g)) instance (Contravariant f, Contravariant g) => Bimodule (->) (,) (Product f g)
deriving via (FromContra (Sum f g)) instance (Contravariant f, Contravariant g) => Bimodule (->) (,) (Sum f g)
deriving via (FromContra (f :+: g)) instance (Contravariant f, Contravariant g) => Bimodule (->) (,) (f :+: g)
deriving via (FromContra (f :*: g)) instance (Contravariant f, Contravariant g) => Bimodule (->) (,) (f :*: g)
deriving via (FromContra (K1 i c)) instance Bimodule (->) (,) (K1 i c)
deriving via (FromContra (Compose f g)) instance (Functor f, Contravariant g) => Bimodule (->) (,) (Compose f g)
deriving via (FromContra (f :.: g)) instance (Functor f, Contravariant g) => Bimodule (->) (,) (f :.: g)
deriving via (FromContra (M1 i c f)) instance Contravariant f => Bimodule (->) (,) (M1 i c f)
