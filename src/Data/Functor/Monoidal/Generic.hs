{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- | Generic deriving of 'Semigroupal' instances via @kind-generics@.
--
-- The @kind-generics@ 'RepK' represents a type parameter structurally,
-- whether it occurs covariantly (as in an @Applicative@) or contravariantly
-- (as in a @Divisible@). One mechanism therefore derives
-- @'Semigroupal' (->) t1 (,)@ for both, across the codomain tensors @(,)@
-- (Applicative and Divisible), @Either@ (Alternative and Decidable), and
-- @These@ (Semialign).
--
-- > data Foo a = Foo (Maybe a) [a]
-- > $(deriveGenericK ''Foo)
-- > deriving via FromGeneric Foo instance Semigroupal (->) (,) (,) Foo
module Data.Functor.Monoidal.Generic
  ( FromGeneric (..),
    GSemigroupalK (..),
  )
where

import Control.Category.Tensor (Associative)
import Data.Functor.Monoidal (Semigroupal (..))
import Generics.Kind
import Prelude

-- | @combine@ over a @kind-generics@ 'RepK', for the product domain tensor
-- @(,)@ and an arbitrary codomain tensor @t1@.
class GSemigroupalK t1 rep where
  gcombineK :: rep (x :&&: LoT0) -> rep (x' :&&: LoT0) -> rep (t1 x x' :&&: LoT0)

-- | The empty constructor.
instance GSemigroupalK t1 U1 where
  gcombineK U1 U1 = U1

-- | Metadata is transparent.
instance (GSemigroupalK t1 f) => GSemigroupalK t1 (M1 i c f) where
  gcombineK (M1 a) (M1 b) = M1 (gcombineK a b)

-- | Combine each side of a product componentwise, for any codomain tensor.
instance (GSemigroupalK t1 f, GSemigroupalK t1 g) => GSemigroupalK t1 (f :*: g) where
  gcombineK (a :*: b) (a' :*: b') = gcombineK a a' :*: gcombineK b b'

-- | The bare parameter, like 'GHC.Generics.Par1'. Only the product tensor
-- @(,)@ has a canonical merge of two values into one.
instance GSemigroupalK (,) (Field Var0) where
  gcombineK (Field x) (Field x') = Field (x, x')

-- | A constant field merges with its 'Monoid'. The value does not mention the
-- parameter, so this holds for any tensor.
instance (Monoid c) => GSemigroupalK t1 (Field (Kon c)) where
  gcombineK (Field c) (Field c') = Field (c <> c')

-- | A sub-functor @g@ applied to the parameter delegates to @g@'s own
-- 'Semigroupal' instance at tensor @t1@. This holds whether @g@ is covariant
-- (Applicative, Alternative, Semialign) or contravariant (Divisible, Decidable).
instance (Semigroupal (->) t1 (,) g) => GSemigroupalK t1 (Field (Kon g :@: Var0)) where
  gcombineK (Field gx) (Field gx') = Field (combine @(->) @t1 @(,) (gx, gx'))

-- | The deriving-via vehicle.
--
-- > deriving via FromGeneric Foo instance Semigroupal (->) t1 (,) Foo
newtype FromGeneric f a = FromGeneric (f a)

instance
  (GenericK f, GSemigroupalK t1 (RepK f), Associative (->) t1) =>
  Semigroupal (->) t1 (,) (FromGeneric f)
  where
  combine ::
    forall x x'.
    (FromGeneric f x, FromGeneric f x') ->
    FromGeneric f (t1 x x')
  combine (FromGeneric fx, FromGeneric fx') =
    FromGeneric
      ( toK @_ @f @(t1 x x' :&&: LoT0)
          (gcombineK (fromK @_ @f @(x :&&: LoT0) fx) (fromK @_ @f @(x' :&&: LoT0) fx'))
      )
