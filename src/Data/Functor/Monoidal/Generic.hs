{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- | Generic deriving of 'Semigroupal' instances via @kind-generics@.
--
-- The @kind-generics@ 'RepK' represents a type parameter structurally,
-- whether it occurs covariantly (as in an @Applicative@) or contravariantly
-- (as in a @Divisible@). One mechanism therefore derives
-- @'Semigroupal' (->) (,) (,)@ for both.
--
-- > data Foo a = Foo (Maybe a) [a]
-- > $(deriveGenericK ''Foo)
-- > deriving via GenericallyK Foo instance Semigroupal (->) (,) (,) Foo
module Data.Functor.Monoidal.Generic
  ( GenericallyK (..),
    GSemigroupalK (..),
  )
where

import Data.Functor.Monoidal (Semigroupal (..))
import Generics.Kind
import Prelude

-- | @combine@ over a @kind-generics@ 'RepK', for the product domain tensor
-- @(,)@.
class GSemigroupalK rep where
  gcombineK :: rep (x :&&: LoT0) -> rep (x' :&&: LoT0) -> rep ((x, x') :&&: LoT0)

-- | The empty constructor.
instance GSemigroupalK U1 where
  gcombineK U1 U1 = U1

-- | Metadata is transparent.
instance (GSemigroupalK f) => GSemigroupalK (M1 i c f) where
  gcombineK (M1 a) (M1 b) = M1 (gcombineK a b)

-- | Combine each side of a product componentwise.
instance (GSemigroupalK f, GSemigroupalK g) => GSemigroupalK (f :*: g) where
  gcombineK (a :*: b) (a' :*: b') = gcombineK a a' :*: gcombineK b b'

-- | The bare parameter, like 'GHC.Generics.Par1'. Pair positionally.
instance GSemigroupalK (Field Var0) where
  gcombineK (Field x) (Field x') = Field (x, x')

-- | A constant field merges with its 'Monoid'.
instance (Monoid c) => GSemigroupalK (Field (Kon c)) where
  gcombineK (Field c) (Field c') = Field (c <> c')

-- | A sub-functor @g@ applied to the parameter delegates to @g@'s own
-- 'Semigroupal' instance. This holds whether @g@ is covariant (Applicative) or
-- contravariant (Divisible).
instance (Semigroupal (->) (,) (,) g) => GSemigroupalK (Field (Kon g :@: Var0)) where
  gcombineK (Field gx) (Field gx') = Field (combine @(->) @(,) @(,) (gx, gx'))

-- | The deriving-via vehicle.
--
-- > deriving via GenericallyK Foo instance Semigroupal (->) (,) (,) Foo
newtype GenericallyK f a = GenericallyK (f a)

instance
  (GenericK f, GSemigroupalK (RepK f)) =>
  Semigroupal (->) (,) (,) (GenericallyK f)
  where
  combine ::
    forall x x'.
    (GenericallyK f x, GenericallyK f x') ->
    GenericallyK f (x, x')
  combine (GenericallyK fx, GenericallyK fx') =
    GenericallyK
      ( toK @_ @f @((x, x') :&&: LoT0)
          (gcombineK (fromK @_ @f @(x :&&: LoT0) fx) (fromK @_ @f @(x' :&&: LoT0) fx'))
      )
