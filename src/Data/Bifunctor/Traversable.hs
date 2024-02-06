{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Data.Bifunctor.Traversable
  ( Traversable (..),
    First (..),
    Second (..),
    -- F (..),
    -- ffirst,
    -- farrow,
    -- sequencedF,
    -- example,
  )
where

--------------------------------------------------------------------------------

import Control.Applicative
import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import Data.Functor.Contravariant (Contravariant (..), Op (..))
import Data.Kind (Constraint, Type)
import GHC.Generics (Generic (..), Generic1, K1 (..), M1 (..), U1 (..), type (:*:) (..))
import Kindly qualified
import Prelude hiding (Traversable (..))

--------------------------------------------------------------------------------

class Traversable hkd where
  sequence :: forall p. (Kindly.Bifunctor Op (->) p, Monoidal (->) (,) () (,) () (,) () p) => hkd p -> p (hkd First) (hkd Second)
  default sequence :: forall p. (Kindly.Bifunctor Op (->) p, Monoidal (->) (,) () (,) () (,) () p, Generic (hkd p), Generic (hkd First), Generic (hkd Second), GTraversable p (Rep (hkd p)) (Rep (hkd First)) (Rep (hkd Second))) => hkd p -> p (hkd First) (hkd Second)
  sequence = Kindly.bimap (Op from) to . gsequence @p @(Rep (hkd p)) @(Rep (hkd First)) @(Rep (hkd Second)) . from

type GTraversable :: (Type -> Type -> Type) -> (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Constraint
class GTraversable p f g h where
  gsequence :: f x -> p (g x) (h x)

instance (Kindly.Bifunctor Op (->) p, GTraversable p f g h) => GTraversable p (M1 _1 _2 f) (M1 _1 _2 g) (M1 _1 _2 h) where
  gsequence :: M1 _1 _2 f x -> p (M1 _1 _2 g x) (M1 _1 _2 h x)
  gsequence (M1 f) = Kindly.bimap (Op unM1) M1 $ gsequence f

instance (Kindly.Bifunctor Op (->) p) => GTraversable p (K1 _1 (p a b)) (K1 _1 (First a b)) (K1 _1 (Second a b)) where
  gsequence :: K1 _1 (p a b) x -> p (K1 _1 (First a b) x) (K1 _1 (Second a b) x)
  gsequence (K1 f) = Kindly.bimap (Op $ unFirst . unK1) (K1 . Second) f

instance (Kindly.Bifunctor Op (->) p, Monoidal (->) (,) () (,) () (,) () p) => GTraversable p U1 U1 U1 where
  gsequence :: U1 x -> p (U1 x) (U1 x)
  gsequence U1 = Kindly.bimap (Op $ const ()) (const U1) $ introduce @_ @_ @() ()

instance (Kindly.Bifunctor Op (->) p, Monoidal (->) (,) () (,) () (,) () p, GTraversable p f1 g1 h1, GTraversable p f2 g2 h2) => GTraversable p (f1 :*: f2) (g1 :*: g2) (h1 :*: h2) where
  gsequence :: (:*:) f1 f2 x -> p ((:*:) g1 g2 x) ((:*:) h1 h2 x)
  gsequence (hkd1 :*: hkd2) =
    let phkd1 = gsequence hkd1
        phkd2 = gsequence hkd2
     in Kindly.bimap (Op $ \(x :*: y) -> (x, y)) (uncurry (:*:)) $ combine (phkd1, phkd2)

--------------------------------------------------------------------------------

type First :: Type -> Type -> Type
newtype First x y = First {unFirst :: x}
  deriving stock (Generic, Generic1, Functor)
  deriving newtype (Bounded, Show, Read, Eq, Ord, Enum, Num, Integral, Real, Semigroup, Monoid)

instance Contravariant (First x) where
  contramap :: (a' -> a) -> First x a -> First x a'
  contramap _ (First x) = First x

instance (Monoid x) => Applicative (First x) where
  pure :: a -> First x a
  pure _ = First mempty

  liftA2 :: (a -> b -> c) -> First x a -> First x b -> First x c
  liftA2 _ (First x) (First x') = First (x <> x')

instance Bifunctor First where
  bimap :: (a -> b) -> (c -> d) -> First a c -> First b d
  bimap f _ (First x) = First (f x)

--------------------------------------------------------------------------------

type Second :: Type -> Type -> Type
newtype Second x y = Second {unSecond :: y}
  deriving stock (Generic, Generic1, Functor)
  deriving newtype (Bounded, Show, Read, Eq, Ord, Enum, Num, Integral, Real, Semigroup, Monoid)

instance Applicative (Second x) where
  pure :: a -> Second x a
  pure = Second

  liftA2 :: (a -> b -> c) -> Second x a -> Second x b -> Second x c
  liftA2 f (Second y) (Second y') = Second (f y y')

instance Bifunctor Second where
  bimap :: (a -> b) -> (c -> d) -> Second a c -> Second b d
  bimap _ g (Second y) = Second (g y)

--------------------------------------------------------------------------------
-- Example:

-- type F :: (Type -> Type -> Type) -> Type
-- data F p = F {foo :: p Int String, bar :: p Bool String, baz :: p Bool Bool}
--   deriving stock (Generic)
--   deriving anyclass (Traversable)

-- deriving instance (forall x y. (Show x, Show y) => Show (p x y)) => Show (F p)

-- farrow :: F (->)
-- farrow = F {foo = show, bar = show, baz = id}

-- ffirst :: F First
-- ffirst = F {foo = First 0, bar = First True, baz = First True}

-- sequencedF :: (->) (F First) (F Second)
-- sequencedF = sequence farrow

-- example :: F Second
-- example = sequencedF ffirst
