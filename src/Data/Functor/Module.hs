module Data.Functor.Module
  ( -- * LeftModule
    LeftModule (..),

    -- * RightModule
    RightModule (..),

    -- * Bimodule
    Bimodule,
  )
where

--------------------------------------------------------------------------------

import Control.Applicative (ZipList)
import Data.Either (Either (..))
import Data.Functor (Functor (..))
import Data.Functor.Compose (Compose)
import Data.Functor.Const (Const)
import Data.Functor.Contravariant (Comparison, Contravariant (..), Equivalence, Op (Op), Predicate)
import Data.Functor.Identity (Identity)
import Data.Functor.Product (Product)
import Data.Functor.Sum (Sum)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (Maybe)
import Data.Monoid (Alt)
import Data.Proxy (Proxy)
import Data.These (These (..))
import Data.Tuple (fst, snd)
import GHC.Generics (K1, M1, Rec1, U1, V1, type (:*:), type (:+:), type (:.:))
import Prelude (IO)

--------------------------------------------------------------------------------

newtype FromContra f a = FromContra (f a)
  deriving newtype (Contravariant)

newtype FromFunctor f a = FromFunctor (f a)
  deriving newtype (Functor)

--------------------------------------------------------------------------------

class LeftModule cat t1 f where
  -- | ==== __Examples__
  --
  -- >>> :t lstrength @(->) @(,) @Predicate (Predicate @Int (> 10))
  -- lstrength @(->) @(,) @Predicate (Predicate @Int (> 10)) :: Predicate (Int, x)
  --
  -- >>> :t lstrength @(->) @Either @[]
  -- lstrength @(->) @Either @[] :: a -> [Either a x]
  --
  -- >>> lstrength @(->) @Either @[] [True, False]
  -- [Left True,Left False]
  lstrength :: cat (f a) (f (t1 a x))

instance (Contravariant f) => LeftModule (->) (,) (FromContra f) where
  lstrength :: FromContra f a -> FromContra f (a, x)
  lstrength = contramap fst

instance (Contravariant f) => LeftModule Op Either (FromContra f) where
  lstrength = Op (contramap Left)

instance (Functor f) => LeftModule (->) Either (FromFunctor f) where
  lstrength :: FromFunctor f a -> FromFunctor f (Either a x)
  lstrength = fmap Left

instance (Functor f) => LeftModule (->) These (FromFunctor f) where
  lstrength :: FromFunctor f a -> FromFunctor f (These a x)
  lstrength = fmap This

instance (Functor f) => LeftModule Op (,) (FromFunctor f) where
  lstrength = Op (fmap fst)

deriving via (FromContra Comparison) instance LeftModule (->) (,) Comparison

deriving via (FromContra Equivalence) instance LeftModule (->) (,) Equivalence

deriving via (FromContra Predicate) instance LeftModule (->) (,) Predicate

deriving via (FromContra (Op a)) instance LeftModule (->) (,) (Op a)

deriving via (FromContra Proxy) instance LeftModule (->) (,) Proxy

deriving via (FromContra U1) instance LeftModule (->) (,) U1

deriving via (FromContra V1) instance LeftModule (->) (,) V1

deriving via (FromContra (Const a)) instance LeftModule (->) (,) (Const a)

deriving via (FromContra (Alt f)) instance (Contravariant f) => LeftModule (->) (,) (Alt f)

deriving via (FromContra (Rec1 f)) instance (Contravariant f) => LeftModule (->) (,) (Rec1 f)

deriving via (FromContra (Product f g)) instance (Contravariant f, Contravariant g) => LeftModule (->) (,) (Product f g)

deriving via (FromContra (Sum f g)) instance (Contravariant f, Contravariant g) => LeftModule (->) (,) (Sum f g)

deriving via (FromContra (f :+: g)) instance (Contravariant f, Contravariant g) => LeftModule (->) (,) (f :+: g)

deriving via (FromContra (f :*: g)) instance (Contravariant f, Contravariant g) => LeftModule (->) (,) (f :*: g)

deriving via (FromContra (K1 i c)) instance LeftModule (->) (,) (K1 i c)

deriving via (FromContra (Compose f g)) instance (Functor f, Contravariant g) => LeftModule (->) (,) (Compose f g)

deriving via (FromContra (f :.: g)) instance (Functor f, Contravariant g) => LeftModule (->) (,) (f :.: g)

deriving via (FromContra (M1 i c f)) instance (Contravariant f) => LeftModule (->) (,) (M1 i c f)

deriving via (FromContra Comparison) instance LeftModule Op Either Comparison

deriving via (FromContra Equivalence) instance LeftModule Op Either Equivalence

deriving via (FromContra Predicate) instance LeftModule Op Either Predicate

deriving via (FromContra (Op a)) instance LeftModule Op Either (Op a)

deriving via (FromContra Proxy) instance LeftModule Op Either Proxy

deriving via (FromContra U1) instance LeftModule Op Either U1

deriving via (FromContra V1) instance LeftModule Op Either V1

deriving via (FromContra (Const a)) instance LeftModule Op Either (Const a)

deriving via (FromContra (Alt f)) instance (Contravariant f) => LeftModule Op Either (Alt f)

deriving via (FromContra (Rec1 f)) instance (Contravariant f) => LeftModule Op Either (Rec1 f)

deriving via (FromContra (Product f g)) instance (Contravariant f, Contravariant g) => LeftModule Op Either (Product f g)

deriving via (FromContra (Sum f g)) instance (Contravariant f, Contravariant g) => LeftModule Op Either (Sum f g)

deriving via (FromContra (f :+: g)) instance (Contravariant f, Contravariant g) => LeftModule Op Either (f :+: g)

deriving via (FromContra (f :*: g)) instance (Contravariant f, Contravariant g) => LeftModule Op Either (f :*: g)

deriving via (FromContra (K1 i c)) instance LeftModule Op Either (K1 i c)

deriving via (FromContra (Compose f g)) instance (Functor f, Contravariant g) => LeftModule Op Either (Compose f g)

deriving via (FromContra (f :.: g)) instance (Functor f, Contravariant g) => LeftModule Op Either (f :.: g)

deriving via (FromContra (M1 i c f)) instance (Contravariant f) => LeftModule Op Either (M1 i c f)

deriving via FromFunctor Identity instance LeftModule (->) Either Identity

deriving via FromFunctor (Compose f g) instance (Functor f, Functor g) => LeftModule (->) Either (Compose f g)

deriving via FromFunctor [] instance LeftModule (->) Either []

deriving via FromFunctor ZipList instance LeftModule (->) Either ZipList

deriving via FromFunctor NonEmpty instance LeftModule (->) Either NonEmpty

deriving via FromFunctor Maybe instance LeftModule (->) Either Maybe

deriving via FromFunctor (Either e) instance LeftModule (->) Either (Either e)

deriving via FromFunctor (These a) instance LeftModule (->) Either (These a)

deriving via FromFunctor IO instance LeftModule (->) Either IO

deriving via FromFunctor (Sum f g) instance (Functor f, Functor g) => LeftModule (->) Either (Sum f g)

deriving via FromFunctor (Product f g) instance (Functor f, Functor g) => LeftModule (->) Either (Product f g)

deriving via (FromFunctor ((,) x1)) instance LeftModule (->) Either ((,) x1)

deriving via (FromFunctor ((,,) x1 x2)) instance LeftModule (->) Either ((,,) x1 x2)

deriving via (FromFunctor ((,,,) x1 x2 x3)) instance LeftModule (->) Either ((,,,) x1 x2 x3)

deriving via FromFunctor Identity instance LeftModule (->) These Identity

deriving via FromFunctor (Compose f g) instance (Functor f, Functor g) => LeftModule (->) These (Compose f g)

deriving via FromFunctor [] instance LeftModule (->) These []

deriving via FromFunctor ZipList instance LeftModule (->) These ZipList

deriving via FromFunctor NonEmpty instance LeftModule (->) These NonEmpty

deriving via FromFunctor Maybe instance LeftModule (->) These Maybe

deriving via FromFunctor (Either e) instance LeftModule (->) These (Either e)

deriving via FromFunctor (These a) instance LeftModule (->) These (These a)

deriving via FromFunctor IO instance LeftModule (->) These IO

deriving via FromFunctor (Sum f g) instance (Functor f, Functor g) => LeftModule (->) These (Sum f g)

deriving via FromFunctor (Product f g) instance (Functor f, Functor g) => LeftModule (->) These (Product f g)

deriving via (FromFunctor ((,) x1)) instance LeftModule (->) These ((,) x1)

deriving via (FromFunctor ((,,) x1 x2)) instance LeftModule (->) These ((,,) x1 x2)

deriving via (FromFunctor ((,,,) x1 x2 x3)) instance LeftModule (->) These ((,,,) x1 x2 x3)

deriving via FromFunctor Identity instance LeftModule Op (,) Identity

deriving via FromFunctor (Compose f g) instance (Functor f, Functor g) => LeftModule Op (,) (Compose f g)

deriving via FromFunctor [] instance LeftModule Op (,) []

deriving via FromFunctor ZipList instance LeftModule Op (,) ZipList

deriving via FromFunctor NonEmpty instance LeftModule Op (,) NonEmpty

deriving via FromFunctor Maybe instance LeftModule Op (,) Maybe

deriving via FromFunctor (Either e) instance LeftModule Op (,) (Either e)

deriving via FromFunctor IO instance LeftModule Op (,) IO

deriving via FromFunctor (Sum f g) instance (Functor f, Functor g) => LeftModule Op (,) (Sum f g)

deriving via FromFunctor (Product f g) instance (Functor f, Functor g) => LeftModule Op (,) (Product f g)

deriving via (FromFunctor ((,) x1)) instance LeftModule Op (,) ((,) x1)

deriving via (FromFunctor ((,,) x1 x2)) instance LeftModule Op (,) ((,,) x1 x2)

deriving via (FromFunctor ((,,,) x1 x2 x3)) instance LeftModule Op (,) ((,,,) x1 x2 x3)

--------------------------------------------------------------------------------

class RightModule cat t1 f where
  -- | ==== __Examples__
  --
  -- >>> :t rstrength @(->) @(,) @Predicate (Predicate @Int (> 10))
  -- rstrength @(->) @(,) @Predicate (Predicate @Int (> 10)) :: Predicate (x, Int)
  --
  -- >>> :t rstrength @(->) @Either @[]
  -- rstrength @(->) @Either @[] :: [a] -> [Either x a]
  -- >>> rstrength @(->) @Either @[] [True, False]
  -- [Right True,Right False]
  rstrength :: cat (f a) (f (t1 x a))

instance (Contravariant f) => RightModule (->) (,) (FromContra f) where
  rstrength :: FromContra f a -> FromContra f (x, a)
  rstrength = contramap snd

instance (Contravariant f) => RightModule Op Either (FromContra f) where
  rstrength :: Op (FromContra f a) (FromContra f (Either x a))
  rstrength = Op (contramap Right)

instance (Functor f) => RightModule (->) Either (FromFunctor f) where
  rstrength :: FromFunctor f a -> FromFunctor f (Either x a)
  rstrength = fmap Right

instance (Functor f) => RightModule (->) These (FromFunctor f) where
  rstrength :: FromFunctor f a -> FromFunctor f (These x a)
  rstrength = fmap That

instance (Functor f) => RightModule Op (,) (FromFunctor f) where
  rstrength :: Op (FromFunctor f a) (FromFunctor f (x, a))
  rstrength = Op (fmap snd)

deriving via (FromContra Comparison) instance RightModule (->) (,) Comparison

deriving via (FromContra Equivalence) instance RightModule (->) (,) Equivalence

deriving via (FromContra Predicate) instance RightModule (->) (,) Predicate

deriving via (FromContra (Op a)) instance RightModule (->) (,) (Op a)

deriving via (FromContra Proxy) instance RightModule (->) (,) Proxy

deriving via (FromContra U1) instance RightModule (->) (,) U1

deriving via (FromContra V1) instance RightModule (->) (,) V1

deriving via (FromContra (Const a)) instance RightModule (->) (,) (Const a)

deriving via (FromContra (Alt f)) instance (Contravariant f) => RightModule (->) (,) (Alt f)

deriving via (FromContra (Rec1 f)) instance (Contravariant f) => RightModule (->) (,) (Rec1 f)

deriving via (FromContra (Product f g)) instance (Contravariant f, Contravariant g) => RightModule (->) (,) (Product f g)

deriving via (FromContra (Sum f g)) instance (Contravariant f, Contravariant g) => RightModule (->) (,) (Sum f g)

deriving via (FromContra (f :+: g)) instance (Contravariant f, Contravariant g) => RightModule (->) (,) (f :+: g)

deriving via (FromContra (f :*: g)) instance (Contravariant f, Contravariant g) => RightModule (->) (,) (f :*: g)

deriving via (FromContra (K1 i c)) instance RightModule (->) (,) (K1 i c)

deriving via (FromContra (Compose f g)) instance (Functor f, Contravariant g) => RightModule (->) (,) (Compose f g)

deriving via (FromContra (f :.: g)) instance (Functor f, Contravariant g) => RightModule (->) (,) (f :.: g)

deriving via (FromContra (M1 i c f)) instance (Contravariant f) => RightModule (->) (,) (M1 i c f)

deriving via (FromContra Comparison) instance RightModule Op Either Comparison

deriving via (FromContra Equivalence) instance RightModule Op Either Equivalence

deriving via (FromContra Predicate) instance RightModule Op Either Predicate

deriving via (FromContra (Op a)) instance RightModule Op Either (Op a)

deriving via (FromContra Proxy) instance RightModule Op Either Proxy

deriving via (FromContra U1) instance RightModule Op Either U1

deriving via (FromContra V1) instance RightModule Op Either V1

deriving via (FromContra (Const a)) instance RightModule Op Either (Const a)

deriving via (FromContra (Alt f)) instance (Contravariant f) => RightModule Op Either (Alt f)

deriving via (FromContra (Rec1 f)) instance (Contravariant f) => RightModule Op Either (Rec1 f)

deriving via (FromContra (Product f g)) instance (Contravariant f, Contravariant g) => RightModule Op Either (Product f g)

deriving via (FromContra (Sum f g)) instance (Contravariant f, Contravariant g) => RightModule Op Either (Sum f g)

deriving via (FromContra (f :+: g)) instance (Contravariant f, Contravariant g) => RightModule Op Either (f :+: g)

deriving via (FromContra (f :*: g)) instance (Contravariant f, Contravariant g) => RightModule Op Either (f :*: g)

deriving via (FromContra (K1 i c)) instance RightModule Op Either (K1 i c)

deriving via (FromContra (Compose f g)) instance (Functor f, Contravariant g) => RightModule Op Either (Compose f g)

deriving via (FromContra (f :.: g)) instance (Functor f, Contravariant g) => RightModule Op Either (f :.: g)

deriving via (FromContra (M1 i c f)) instance (Contravariant f) => RightModule Op Either (M1 i c f)

deriving via FromFunctor Identity instance RightModule (->) Either Identity

deriving via FromFunctor (Compose f g) instance (Functor f, Functor g) => RightModule (->) Either (Compose f g)

deriving via FromFunctor [] instance RightModule (->) Either []

deriving via FromFunctor ZipList instance RightModule (->) Either ZipList

deriving via FromFunctor NonEmpty instance RightModule (->) Either NonEmpty

deriving via FromFunctor Maybe instance RightModule (->) Either Maybe

deriving via FromFunctor (Either e) instance RightModule (->) Either (Either e)

deriving via FromFunctor (These a) instance RightModule (->) Either (These a)

deriving via FromFunctor IO instance RightModule (->) Either IO

deriving via FromFunctor (Sum f g) instance (Functor f, Functor g) => RightModule (->) Either (Sum f g)

deriving via FromFunctor (Product f g) instance (Functor f, Functor g) => RightModule (->) Either (Product f g)

deriving via (FromFunctor ((,) x1)) instance RightModule (->) Either ((,) x1)

deriving via (FromFunctor ((,,) x1 x2)) instance RightModule (->) Either ((,,) x1 x2)

deriving via (FromFunctor ((,,,) x1 x2 x3)) instance RightModule (->) Either ((,,,) x1 x2 x3)

deriving via FromFunctor Identity instance RightModule (->) These Identity

deriving via FromFunctor (Compose f g) instance (Functor f, Functor g) => RightModule (->) These (Compose f g)

deriving via FromFunctor [] instance RightModule (->) These []

deriving via FromFunctor ZipList instance RightModule (->) These ZipList

deriving via FromFunctor NonEmpty instance RightModule (->) These NonEmpty

deriving via FromFunctor Maybe instance RightModule (->) These Maybe

deriving via FromFunctor (Either e) instance RightModule (->) These (Either e)

deriving via FromFunctor (These a) instance RightModule (->) These (These a)

deriving via FromFunctor IO instance RightModule (->) These IO

deriving via FromFunctor (Sum f g) instance (Functor f, Functor g) => RightModule (->) These (Sum f g)

deriving via FromFunctor (Product f g) instance (Functor f, Functor g) => RightModule (->) These (Product f g)

deriving via (FromFunctor ((,) x1)) instance RightModule (->) These ((,) x1)

deriving via (FromFunctor ((,,) x1 x2)) instance RightModule (->) These ((,,) x1 x2)

deriving via (FromFunctor ((,,,) x1 x2 x3)) instance RightModule (->) These ((,,,) x1 x2 x3)

deriving via FromFunctor Identity instance RightModule Op (,) Identity

deriving via FromFunctor (Compose f g) instance (Functor f, Functor g) => RightModule Op (,) (Compose f g)

deriving via FromFunctor [] instance RightModule Op (,) []

deriving via FromFunctor ZipList instance RightModule Op (,) ZipList

deriving via FromFunctor NonEmpty instance RightModule Op (,) NonEmpty

deriving via FromFunctor Maybe instance RightModule Op (,) Maybe

deriving via FromFunctor (Either e) instance RightModule Op (,) (Either e)

deriving via FromFunctor IO instance RightModule Op (,) IO

deriving via FromFunctor (Sum f g) instance (Functor f, Functor g) => RightModule Op (,) (Sum f g)

deriving via FromFunctor (Product f g) instance (Functor f, Functor g) => RightModule Op (,) (Product f g)

deriving via (FromFunctor ((,) x1)) instance RightModule Op (,) ((,) x1)

deriving via (FromFunctor ((,,) x1 x2)) instance RightModule Op (,) ((,,) x1 x2)

deriving via (FromFunctor ((,,,) x1 x2 x3)) instance RightModule Op (,) ((,,,) x1 x2 x3)

--------------------------------------------------------------------------------

class (LeftModule cat t1 f, RightModule cat t1 f) => Bimodule cat t1 f

instance (Contravariant f) => Bimodule (->) (,) (FromContra f)

instance (Contravariant f) => Bimodule Op Either (FromContra f)

instance (Functor f) => Bimodule (->) Either (FromFunctor f)

instance (Functor f) => Bimodule (->) These (FromFunctor f)

instance (Functor f) => Bimodule Op (,) (FromFunctor f)

deriving via (FromContra Comparison) instance Bimodule (->) (,) Comparison

deriving via (FromContra Equivalence) instance Bimodule (->) (,) Equivalence

deriving via (FromContra Predicate) instance Bimodule (->) (,) Predicate

deriving via (FromContra (Op a)) instance Bimodule (->) (,) (Op a)

deriving via (FromContra Proxy) instance Bimodule (->) (,) Proxy

deriving via (FromContra U1) instance Bimodule (->) (,) U1

deriving via (FromContra V1) instance Bimodule (->) (,) V1

deriving via (FromContra (Const a)) instance Bimodule (->) (,) (Const a)

deriving via (FromContra (Alt f)) instance (Contravariant f) => Bimodule (->) (,) (Alt f)

deriving via (FromContra (Rec1 f)) instance (Contravariant f) => Bimodule (->) (,) (Rec1 f)

deriving via (FromContra (Product f g)) instance (Contravariant f, Contravariant g) => Bimodule (->) (,) (Product f g)

deriving via (FromContra (Sum f g)) instance (Contravariant f, Contravariant g) => Bimodule (->) (,) (Sum f g)

deriving via (FromContra (f :+: g)) instance (Contravariant f, Contravariant g) => Bimodule (->) (,) (f :+: g)

deriving via (FromContra (f :*: g)) instance (Contravariant f, Contravariant g) => Bimodule (->) (,) (f :*: g)

deriving via (FromContra (K1 i c)) instance Bimodule (->) (,) (K1 i c)

deriving via (FromContra (Compose f g)) instance (Functor f, Contravariant g) => Bimodule (->) (,) (Compose f g)

deriving via (FromContra (f :.: g)) instance (Functor f, Contravariant g) => Bimodule (->) (,) (f :.: g)

deriving via (FromContra (M1 i c f)) instance (Contravariant f) => Bimodule (->) (,) (M1 i c f)

deriving via (FromContra Comparison) instance Bimodule Op Either Comparison

deriving via (FromContra Equivalence) instance Bimodule Op Either Equivalence

deriving via (FromContra Predicate) instance Bimodule Op Either Predicate

deriving via (FromContra (Op a)) instance Bimodule Op Either (Op a)

deriving via (FromContra Proxy) instance Bimodule Op Either Proxy

deriving via (FromContra U1) instance Bimodule Op Either U1

deriving via (FromContra V1) instance Bimodule Op Either V1

deriving via (FromContra (Const a)) instance Bimodule Op Either (Const a)

deriving via (FromContra (Alt f)) instance (Contravariant f) => Bimodule Op Either (Alt f)

deriving via (FromContra (Rec1 f)) instance (Contravariant f) => Bimodule Op Either (Rec1 f)

deriving via (FromContra (Product f g)) instance (Contravariant f, Contravariant g) => Bimodule Op Either (Product f g)

deriving via (FromContra (Sum f g)) instance (Contravariant f, Contravariant g) => Bimodule Op Either (Sum f g)

deriving via (FromContra (f :+: g)) instance (Contravariant f, Contravariant g) => Bimodule Op Either (f :+: g)

deriving via (FromContra (f :*: g)) instance (Contravariant f, Contravariant g) => Bimodule Op Either (f :*: g)

deriving via (FromContra (K1 i c)) instance Bimodule Op Either (K1 i c)

deriving via (FromContra (Compose f g)) instance (Functor f, Contravariant g) => Bimodule Op Either (Compose f g)

deriving via (FromContra (f :.: g)) instance (Functor f, Contravariant g) => Bimodule Op Either (f :.: g)

deriving via (FromContra (M1 i c f)) instance (Contravariant f) => Bimodule Op Either (M1 i c f)

deriving via FromFunctor Identity instance Bimodule (->) Either Identity

deriving via FromFunctor (Compose f g) instance (Functor f, Functor g) => Bimodule (->) Either (Compose f g)

deriving via FromFunctor [] instance Bimodule (->) Either []

deriving via FromFunctor ZipList instance Bimodule (->) Either ZipList

deriving via FromFunctor NonEmpty instance Bimodule (->) Either NonEmpty

deriving via FromFunctor Maybe instance Bimodule (->) Either Maybe

deriving via FromFunctor (Either e) instance Bimodule (->) Either (Either e)

deriving via FromFunctor (These a) instance Bimodule (->) Either (These a)

deriving via FromFunctor IO instance Bimodule (->) Either IO

deriving via FromFunctor (Sum f g) instance (Functor f, Functor g) => Bimodule (->) Either (Sum f g)

deriving via FromFunctor (Product f g) instance (Functor f, Functor g) => Bimodule (->) Either (Product f g)

deriving via (FromFunctor ((,) x1)) instance Bimodule (->) Either ((,) x1)

deriving via (FromFunctor ((,,) x1 x2)) instance Bimodule (->) Either ((,,) x1 x2)

deriving via (FromFunctor ((,,,) x1 x2 x3)) instance Bimodule (->) Either ((,,,) x1 x2 x3)

deriving via FromFunctor Identity instance Bimodule (->) These Identity

deriving via FromFunctor (Compose f g) instance (Functor f, Functor g) => Bimodule (->) These (Compose f g)

deriving via FromFunctor [] instance Bimodule (->) These []

deriving via FromFunctor ZipList instance Bimodule (->) These ZipList

deriving via FromFunctor NonEmpty instance Bimodule (->) These NonEmpty

deriving via FromFunctor Maybe instance Bimodule (->) These Maybe

deriving via FromFunctor (Either e) instance Bimodule (->) These (Either e)

deriving via FromFunctor (These a) instance Bimodule (->) These (These a)

deriving via FromFunctor IO instance Bimodule (->) These IO

deriving via FromFunctor (Sum f g) instance (Functor f, Functor g) => Bimodule (->) These (Sum f g)

deriving via FromFunctor (Product f g) instance (Functor f, Functor g) => Bimodule (->) These (Product f g)

deriving via (FromFunctor ((,) x1)) instance Bimodule (->) These ((,) x1)

deriving via (FromFunctor ((,,) x1 x2)) instance Bimodule (->) These ((,,) x1 x2)

deriving via (FromFunctor ((,,,) x1 x2 x3)) instance Bimodule (->) These ((,,,) x1 x2 x3)

deriving via FromFunctor Identity instance Bimodule Op (,) Identity

deriving via FromFunctor (Compose f g) instance (Functor f, Functor g) => Bimodule Op (,) (Compose f g)

deriving via FromFunctor [] instance Bimodule Op (,) []

deriving via FromFunctor ZipList instance Bimodule Op (,) ZipList

deriving via FromFunctor NonEmpty instance Bimodule Op (,) NonEmpty

deriving via FromFunctor Maybe instance Bimodule Op (,) Maybe

deriving via FromFunctor (Either e) instance Bimodule Op (,) (Either e)

deriving via FromFunctor IO instance Bimodule Op (,) IO

deriving via FromFunctor (Sum f g) instance (Functor f, Functor g) => Bimodule Op (,) (Sum f g)

deriving via FromFunctor (Product f g) instance (Functor f, Functor g) => Bimodule Op (,) (Product f g)

deriving via (FromFunctor ((,) x1)) instance Bimodule Op (,) ((,) x1)

deriving via (FromFunctor ((,,) x1 x2)) instance Bimodule Op (,) ((,,) x1 x2)

deriving via (FromFunctor ((,,,) x1 x2 x3)) instance Bimodule Op (,) ((,,,) x1 x2 x3)
