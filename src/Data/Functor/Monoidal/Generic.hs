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
    FromRepresentable (..),
    GSemigroupalK (..),
    GCosemigroupalK (..),
    GUnitalK (..),
  )
where

import Control.Category.Tensor (Associative, Tensor)
import Data.Distributive (Distributive)
import Data.Functor.Contravariant (Op (..))
import Data.Functor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
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
  gcombineK (Field a) (Field b) = Field (combine @(->) @t1 @(,) (a, b))

-- | A nested field @f (g a)@. Product-combine the outer functor, then map the
-- inner combine over it.
instance
  (Semigroupal (->) (,) (,) f, Functor f, Semigroupal (->) t1 (,) g) =>
  GSemigroupalK t1 (Field (Kon f :@: (Kon g :@: Var0)))
  where
  gcombineK (Field a) (Field b) =
    Field (fmap (combine @(->) @t1 @(,)) (combine @(->) @(,) @(,) (a, b)))

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

--------------------------------------------------------------------------------
-- Split (Op), the comonoidal direction for the product tensor

-- | @combine@ over @Op@ for the product tensor. This splits one structure into
-- two, @rep ((x, x') :&&: LoT0) -> (rep (x :&&: LoT0), rep (x' :&&: LoT0))@.
class GCosemigroupalK rep where
  gcosplitK :: rep ((x, x') :&&: LoT0) -> (rep (x :&&: LoT0), rep (x' :&&: LoT0))

instance GCosemigroupalK U1 where
  gcosplitK U1 = (U1, U1)

instance (GCosemigroupalK f) => GCosemigroupalK (M1 i c f) where
  gcosplitK (M1 a) = let (l, r) = gcosplitK a in (M1 l, M1 r)

instance (GCosemigroupalK f, GCosemigroupalK g) => GCosemigroupalK (f :*: g) where
  gcosplitK (a :*: b) =
    let (al, ar) = gcosplitK a
        (bl, br) = gcosplitK b
     in (al :*: bl, ar :*: br)

-- | Splitting a sum is total. The single input constructor determines matched
-- outputs, so @:+:@ has none of the mismatched-constructor trouble that blocks
-- the combine direction.
instance (GCosemigroupalK f, GCosemigroupalK g) => GCosemigroupalK (f :+: g) where
  gcosplitK (L1 a) = let (l, r) = gcosplitK a in (L1 l, L1 r)
  gcosplitK (R1 b) = let (l, r) = gcosplitK b in (R1 l, R1 r)

-- | The bare parameter splits the pair.
instance GCosemigroupalK (Field Var0) where
  gcosplitK (Field (x, x')) = (Field x, Field x')

-- | A constant field is duplicated.
instance GCosemigroupalK (Field (Kon c)) where
  gcosplitK (Field c) = (Field c, Field c)

-- | A sub-functor uses the functorial unzip @fmap fst@ and @fmap snd@. This is
-- total for any 'Functor' and gives the standalone split.
instance (Functor g) => GCosemigroupalK (Field (Kon g :@: Var0)) where
  gcosplitK (Field gxx) = (Field (fmap fst gxx), Field (fmap snd gxx))

-- | A nested field @f (g a)@ splits with a double @fmap@.
instance (Functor f, Functor g) => GCosemigroupalK (Field (Kon f :@: (Kon g :@: Var0))) where
  gcosplitK (Field fgxx) = (Field (fmap (fmap fst) fgxx), Field (fmap (fmap snd) fgxx))

-- | The generic split, shared by both vehicles below.
gsplit ::
  forall f x x'.
  (GenericK f, GCosemigroupalK (RepK f)) =>
  f (x, x') ->
  (f x, f x')
gsplit fxx =
  let (l, r) = gcosplitK (fromK @_ @f @((x, x') :&&: LoT0) fxx)
   in (toK @_ @f @(x :&&: LoT0) l, toK @_ @f @(x' :&&: LoT0) r)

-- | The standalone split.
--
-- > deriving via FromGeneric Foo instance Semigroupal Op (,) (,) Foo
--
-- This has unzip semantics and is total, even on sums. It does not always
-- invert the cartesian @combine@.
instance
  (GenericK f, GCosemigroupalK (RepK f)) =>
  Semigroupal Op (,) (,) (FromGeneric f)
  where
  combine :: Op (FromGeneric f x, FromGeneric f x') (FromGeneric f (x, x'))
  combine = Op (\(FromGeneric fxx) -> let (a, b) = gsplit fxx in (FromGeneric a, FromGeneric b))

-- | The coherent split, gated on 'Distributive'. A split inverts the cartesian
-- @combine@ exactly when the functor is representable, so this vehicle compiles
-- only for representable functors.
--
-- > deriving via FromRepresentable Foo instance Semigroupal Op (,) (,) Foo
newtype FromRepresentable f a = FromRepresentable (f a)

instance
  (GenericK f, GCosemigroupalK (RepK f), Distributive f) =>
  Semigroupal Op (,) (,) (FromRepresentable f)
  where
  combine :: Op (FromRepresentable f x, FromRepresentable f x') (FromRepresentable f (x, x'))
  combine = Op (\(FromRepresentable fxx) -> let (a, b) = gsplit fxx in (FromRepresentable a, FromRepresentable b))

--------------------------------------------------------------------------------
-- Unital and Monoidal

-- | @introduce@ over a @kind-generics@ 'RepK', building the unit-filled
-- structure at a codomain unit @i1@. This is @()@ for the product tensor
-- (Applicative and Divisible) and @Void@ for @Either@ and @These@ (Alternative
-- and Decidable).
class GUnitalK i1 rep where
  gintroduceK :: rep (i1 :&&: LoT0)

instance GUnitalK i1 U1 where
  gintroduceK = U1

instance (GUnitalK i1 f) => GUnitalK i1 (M1 i c f) where
  gintroduceK = M1 gintroduceK

instance (GUnitalK i1 f, GUnitalK i1 g) => GUnitalK i1 (f :*: g) where
  gintroduceK = gintroduceK :*: gintroduceK

-- | A bare parameter can only be introduced at the product unit @()@, the one
-- unit object with a canonical inhabitant. There is no value of @Void@ to place
-- here, so a type with a bare-parameter field has no @Either@/@These@ unit.
instance GUnitalK () (Field Var0) where
  gintroduceK = Field ()

-- | A constant field is the 'Monoid' identity, at any unit.
instance (Monoid c) => GUnitalK i1 (Field (Kon c)) where
  gintroduceK = Field mempty

-- | A sub-functor delegates to its own 'Unital' instance at the same unit.
instance (Unital (->) i1 () g) => GUnitalK i1 (Field (Kon g :@: Var0)) where
  gintroduceK = Field (introduce @(->) @i1 @() ())

-- | A nested field @f (g i1)@: the outer functor at the product unit, the inner
-- at @i1@, mirroring the nested @combine@.
instance
  (Functor f, Unital (->) () () f, Unital (->) i1 () g) =>
  GUnitalK i1 (Field (Kon f :@: (Kon g :@: Var0)))
  where
  gintroduceK =
    Field (fmap (const (introduce @(->) @i1 @() ())) (introduce @(->) @() @() ()))

-- | The unit vehicle, at any codomain unit @i1@:
--
-- > deriving via FromGeneric Foo instance Unital (->) () () Foo
-- > deriving via FromGeneric Foo instance Unital (->) Void () Foo
instance (GenericK f, GUnitalK i1 (RepK f)) => Unital (->) i1 () (FromGeneric f) where
  introduce :: () -> FromGeneric f i1
  introduce () = FromGeneric (toK @_ @f @(i1 :&&: LoT0) gintroduceK)

-- | @Monoidal@ falls out of 'Semigroupal' plus 'Unital', for any codomain
-- tensor @t1@ paired with its unit @i1@:
--
-- > deriving via FromGeneric Foo instance Monoidal (->) (,) () (,) () Foo
-- > deriving via FromGeneric Foo instance Monoidal (->) Either Void (,) () Foo
instance
  (GenericK f, GSemigroupalK t1 (RepK f), GUnitalK i1 (RepK f), Tensor (->) t1 i1) =>
  Monoidal (->) t1 i1 (,) () (FromGeneric f)
