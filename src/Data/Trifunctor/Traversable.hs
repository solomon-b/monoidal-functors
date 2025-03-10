{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Data.Trifunctor.Traversable
  ( Traversable (..),
    First (..),
    Second (..),
  )
where

--------------------------------------------------------------------------------

import Control.Applicative
import Data.Bifunctor (Bifunctor (..))
import Data.Functor.Contravariant (Contravariant (..), Op (..))
import Data.Kind (Constraint, Type)
import Data.Trifunctor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import GHC.Generics (Generic (..), Generic1, K1 (..), M1 (..), U1 (..), type (:*:) (..))
import Kindly qualified
import Prelude hiding (Traversable)

--------------------------------------------------------------------------------

class Traversable hkd where
  sequence :: forall p. (Kindly.Trifunctor (->) Op (->) p, Monoidal (->) (,) () (,) () (,) () (,) () p) => hkd p -> p (hkd First) (hkd Second) (hkd Third)
  default sequence ::
    forall p.
    ( Kindly.MapArg3 (->) Op (->) p,
      Monoidal (->) (,) () (,) () (,) () (,) () p,
      Generic (hkd p),
      Generic (hkd First),
      Generic (hkd Second),
      Generic (hkd Third),
      GTraversable p (Rep (hkd p)) (Rep (hkd First)) (Rep (hkd Second)) (Rep (hkd Third))
    ) =>
    hkd p ->
    p (hkd First) (hkd Second) (hkd Third)
  sequence = Kindly.trimap to (Op from) to . gsequence @p @(Rep (hkd p)) @(Rep (hkd First)) @(Rep (hkd Second)) . from

type GTraversable :: (Type -> Type -> Type -> Type) -> (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Constraint
class GTraversable p f g h i where
  gsequence :: f x -> p (g x) (h x) (i x)

instance (Kindly.Trifunctor (->) Op (->) p, GTraversable p f g h i) => GTraversable p (M1 _1 _2 f) (M1 _1 _2 g) (M1 _1 _2 h) (M1 _1 _2 i) where
  gsequence :: M1 _1 _2 f x -> p (M1 _1 _2 g x) (M1 _1 _2 h x) (M1 _1 _2 i x)
  gsequence (M1 f) = Kindly.trimap M1 (Op unM1) M1 $ gsequence @p @f @g @h @i f

instance (Kindly.Trifunctor (->) Op (->) p) => GTraversable p (K1 _1 (p a b c)) (K1 _1 (First a b c)) (K1 _1 (Second a b c)) (K1 _1 (Third a b c)) where
  gsequence :: K1 _1 (p a b c) x -> p (K1 _1 (First a b c) x) (K1 _1 (Second a b c) x) (K1 _1 (Third a b c) x)
  gsequence (K1 f) = Kindly.trimap (K1 . First) (Op $ unSecond . unK1) (K1 . Third) f

instance (Kindly.Trifunctor (->) Op (->) p, Monoidal (->) (,) () (,) () (,) () (,) () p) => GTraversable p U1 U1 U1 U1 where
  gsequence :: U1 x -> p (U1 x) (U1 x) (U1 x)
  gsequence U1 = Kindly.trimap (const U1) (Op $ const ()) (const U1) $ introduce @_ @() @() @() ()

instance
  (Kindly.Trifunctor (->) Op (->) p, Monoidal (->) (,) () (,) () (,) () (,) () p, GTraversable p f1 g1 h1 j1, GTraversable p f2 g2 h2 j2) =>
  GTraversable p (f1 :*: f2) (g1 :*: g2) (h1 :*: h2) (j1 :*: j2)
  where
  gsequence :: (:*:) f1 f2 x -> p ((:*:) g1 g2 x) ((:*:) h1 h2 x) ((:*:) j1 j2 x)
  gsequence (hkd1 :*: hkd2) =
    let phkd1 = gsequence @p @f1 @g1 @h1 @j1 hkd1
        phkd2 = gsequence @p @f2 @g2 @h2 @j2 hkd2
     in Kindly.trimap (uncurry (:*:)) (Op (\(x :*: y) -> (x, y))) (uncurry (:*:)) $ combine @_ @(,) @(,) @(,) (phkd1, phkd2)

--------------------------------------------------------------------------------

type First :: Type -> Type -> Type -> Type
newtype First x y z = First {unFirst :: x}
  deriving stock (Generic, Generic1, Functor)
  deriving newtype (Bounded, Show, Read, Eq, Ord, Enum, Num, Integral, Real, Semigroup, Monoid)

instance Contravariant (First x y) where
  contramap :: (a' -> a) -> First x y a -> First x y a'
  contramap _ (First x) = First x

instance (Monoid x) => Applicative (First x y) where
  pure :: a -> First x y a
  pure _ = First mempty

  liftA2 :: (a -> b -> c) -> First x y a -> First x y b -> First x y c
  liftA2 _ (First x) (First x') = First (x <> x')

instance Bifunctor (First x) where
  bimap :: (a -> b) -> (c -> d) -> First x a c -> First x b d
  bimap _ _ (First x) = First x

--------------------------------------------------------------------------------

type Second :: Type -> Type -> Type -> Type
newtype Second x y z = Second {unSecond :: y}
  deriving stock (Generic, Generic1, Functor)
  deriving newtype (Bounded, Show, Read, Eq, Ord, Enum, Num, Integral, Real, Semigroup, Monoid)

instance (Monoid y) => Applicative (Second x y) where
  pure :: a -> Second x y a
  pure _ = Second mempty

  liftA2 :: (a -> b -> c) -> Second x y a -> Second x y b -> Second x y c
  liftA2 _ (Second y) (Second y') = Second (y <> y')

instance Bifunctor (Second x) where
  bimap :: (a -> b) -> (c -> d) -> Second x a c -> Second x b d
  bimap f _ (Second a) = Second $ f a

--------------------------------------------------------------------------------

type Third :: Type -> Type -> Type -> Type
newtype Third x y z = Third {unThird :: z}
  deriving stock (Generic, Generic1, Functor)
  deriving newtype (Bounded, Show, Read, Eq, Ord, Enum, Num, Integral, Real, Semigroup, Monoid)

instance Applicative (Third x y) where
  pure :: a -> Third x y a
  pure = Third

  liftA2 :: (a -> b -> c) -> Third x y a -> Third x y b -> Third x y c
  liftA2 f (Third y) (Third y') = Third (f y y')

instance Bifunctor (Third x) where
  bimap :: (a -> b) -> (c -> d) -> Third x a c -> Third x b d
  bimap _ g (Third y) = Third (g y)
