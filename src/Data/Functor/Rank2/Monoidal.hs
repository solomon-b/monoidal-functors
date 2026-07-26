{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}

-- | Rank-2 monoidal functors: the analogue of "Data.Functor.Monoidal" one level
-- up, for higher-kinded data @b :: (Type -> Type) -> Type@.
--
-- A rank-2 functor is a functor \(B : [\mathcal{Hask}, \mathcal{Hask}] \to \mathcal{Hask}\)
-- from the functor category to @Hask@; @b f@ reinterprets each field of the
-- record @b@ through @f@. "Kindly.Rank2" already supplies the functorial action
-- (@'Kindly.bmap' :: (forall x. f x -> g x) -> b f -> b g@). This module adds the
-- /monoidal/ structure on top of it, the same way "Data.Functor.Monoidal" adds
-- 'Data.Functor.Monoidal.combine' \/ 'Data.Functor.Monoidal.introduce' on top of
-- an ordinary 'Functor'.
--
-- The classes keep the same parameter shape as their rank-1 siblings, only
-- lifted a kind: the domain tensor @t1@ now acts on functors (@'Data.Functor.Product.Product'@
-- is the cartesian product of the functor category) while the codomain tensor
-- @t0@ still acts on @Hask@ (@(,)@). At the covariant instantiation
-- @'Monoidal' (->) 'Data.Functor.Product.Product' 'Data.Proxy.Proxy' (,) () b@ this is
-- @barbies@' @ApplicativeB@:
--
-- * 'combine' is @bprod :: b f -> b g -> b (Product f g)@ (uncurried), and
-- * 'introduce' is @bpure Proxy :: b Proxy@, the record whose every field is
--   'Data.Proxy.Proxy'.
--
-- The generic default covers records whose fields all have the shape @f a@.
-- Sums and nested HKD fields are not supported, matching
-- "Data.Functor.Rank2.Traversable".
module Data.Functor.Rank2.Monoidal
  ( -- * Semigroupal
    Semigroupal (..),

    -- * Unital
    Unital (..),

    -- * Monoidal
    Monoidal,
  )
where

--------------------------------------------------------------------------------

import Data.Functor.Product (Product (..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import Data.Type.Equality (type (~))
import GHC.Generics (Generic (..), K1 (..), M1 (..), U1 (..), type (:*:) (..))

--------------------------------------------------------------------------------

-- | The rank-2 analogue of 'Data.Functor.Monoidal.Semigroupal'. Given a
-- monoidal structure \(\otimes\) on the functor category and \(\bullet\) on
-- @Hask@, a rank-2 functor @b@ is 'Semigroupal' if it carries a natural
-- transformation \(\phi_{f,g} : b\ f \bullet b\ g \to b\ (f \otimes g)\), which
-- we call 'combine'.
--
-- The parameters mirror the rank-1 class one kind up:
--
-- * @cat@ is the codomain category (@Hask@).
-- * @t1@ is the domain tensor, acting on functors (e.g. 'Product').
-- * @t0@ is the codomain tensor, acting on @Hask@ (e.g. @(,)@).
-- * @b@ is the higher-kinded record.
type Semigroupal ::
  (Type -> Type -> Type) ->
  ((Type -> Type) -> (Type -> Type) -> (Type -> Type)) ->
  (Type -> Type -> Type) ->
  ((Type -> Type) -> Type) ->
  Constraint
class Semigroupal cat t1 t0 b where
  -- | Zip two records field-by-field, pairing each field's interpretations
  -- under the domain tensor. At the covariant 'Product' instantiation this is
  -- @barbies@' uncurried @bprod@.
  combine :: forall f g. cat (t0 (b f) (b g)) (b (t1 f g))
  default combine ::
    forall f g.
    ( cat ~ (->),
      t1 ~ Product,
      t0 ~ (,),
      Generic (b f),
      Generic (b g),
      Generic (b (Product f g)),
      GSemigroupal (Rep (b f)) (Rep (b g)) (Rep (b (Product f g)))
    ) =>
    cat (t0 (b f) (b g)) (b (t1 f g))
  combine (bf, bg) = to (gcombine (from bf, from bg))

--------------------------------------------------------------------------------

-- | The rank-2 analogue of 'Data.Functor.Monoidal.Unital'. A rank-2 functor
-- @b@ is 'Unital' if it carries a morphism from the codomain unit to @b@ at the
-- domain unit, which we call 'introduce'.
--
-- * @cat@ is the codomain category (@Hask@).
-- * @i1@ is the domain unit, a functor (the unit of @t1@; 'Proxy' for 'Product').
-- * @i0@ is the codomain unit (the unit of @t0@; @()@ for @(,)@).
-- * @b@ is the higher-kinded record.
type Unital ::
  (Type -> Type -> Type) ->
  (Type -> Type) ->
  Type ->
  ((Type -> Type) -> Type) ->
  Constraint
class Unital cat i1 i0 b where
  -- | The unit record. At the covariant 'Proxy' instantiation this is
  -- @barbies@' @bpure Proxy@: the record whose every field is 'Proxy'.
  introduce :: cat i0 (b i1)
  default introduce ::
    ( cat ~ (->),
      i1 ~ Proxy,
      i0 ~ (),
      Generic (b Proxy),
      GUnital (Rep (b Proxy))
    ) =>
    cat i0 (b i1)
  introduce () = to gintroduce

--------------------------------------------------------------------------------

-- | The rank-2 analogue of 'Data.Functor.Monoidal.Monoidal'. A rank-2 functor
-- that is both 'Semigroupal' and 'Unital', preserving the monoidal structure
-- between the functor category and @Hask@. At
-- @'Monoidal' (->) 'Product' 'Proxy' (,) () b@ this is @barbies@' @ApplicativeB@.
type Monoidal ::
  (Type -> Type -> Type) ->
  ((Type -> Type) -> (Type -> Type) -> (Type -> Type)) ->
  (Type -> Type) ->
  (Type -> Type -> Type) ->
  Type ->
  ((Type -> Type) -> Type) ->
  Constraint
class
  ( Semigroupal cat t1 t0 b,
    Unital cat i1 i0 b
  ) =>
  Monoidal cat t1 i1 t0 i0 b

--------------------------------------------------------------------------------
-- Generic derivation for the covariant 'Product' \/ 'Proxy' instantiation.

-- | Generic worker for 'combine' at the covariant 'Product' tensor. The three
-- representations are @'Rep' (b f)@, @'Rep' (b g)@, and @'Rep' (b (Product f g))@;
-- structurally identical up to the field interpretation, which the 'K1' case
-- fuses into a 'Pair'.
type GSemigroupal :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Constraint
class GSemigroupal repf repg reph where
  gcombine :: (repf x, repg x) -> reph x

instance (GSemigroupal repf repg reph) => GSemigroupal (M1 i c repf) (M1 i c repg) (M1 i c reph) where
  gcombine :: (M1 i c repf x, M1 i c repg x) -> M1 i c reph x
  gcombine (M1 a, M1 b) = M1 (gcombine (a, b))

instance (GSemigroupal f1 g1 h1, GSemigroupal f2 g2 h2) => GSemigroupal (f1 :*: f2) (g1 :*: g2) (h1 :*: h2) where
  gcombine :: ((f1 :*: f2) x, (g1 :*: g2) x) -> (h1 :*: h2) x
  gcombine (a1 :*: a2, b1 :*: b2) = gcombine (a1, b1) :*: gcombine (a2, b2)

instance GSemigroupal (K1 i (p a)) (K1 i (q a)) (K1 i (Product p q a)) where
  gcombine :: (K1 i (p a) x, K1 i (q a) x) -> K1 i (Product p q a) x
  gcombine (K1 pa, K1 qa) = K1 (Pair pa qa)

instance GSemigroupal U1 U1 U1 where
  gcombine :: (U1 x, U1 x) -> U1 x
  gcombine (U1, U1) = U1

--------------------------------------------------------------------------------

-- | Generic worker for 'introduce' at the covariant 'Proxy' unit: fills every
-- field of @'Rep' (b Proxy)@ with 'Proxy'.
type GUnital :: (Type -> Type) -> Constraint
class GUnital rep where
  gintroduce :: rep x

instance (GUnital rep) => GUnital (M1 i c rep) where
  gintroduce :: M1 i c rep x
  gintroduce = M1 gintroduce

instance (GUnital f, GUnital g) => GUnital (f :*: g) where
  gintroduce :: (f :*: g) x
  gintroduce = gintroduce :*: gintroduce

instance GUnital (K1 i (Proxy a)) where
  gintroduce :: K1 i (Proxy a) x
  gintroduce = K1 Proxy

instance GUnital U1 where
  gintroduce :: U1 x
  gintroduce = U1
