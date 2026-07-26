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
-- lifted a kind: the domain tensor @t1@ now acts on functors while the codomain
-- tensor @t0@ still acts on @Hask@. A product-shaped record is monoidal at three
-- instantiations, all derivable from the record's 'GHC.Generics' structure:
--
-- * __Covariant product__, @'Monoidal' (->) 'Product' 'Data.Proxy.Proxy' (,) () b@.
--   This is @barbies@' @ApplicativeB@: 'combine' zips two records field-wise into
--   'Data.Functor.Product.Pair's (@bprod@) and 'introduce' fills every field with
--   'Data.Proxy.Proxy' (@bpure Proxy@).
--
-- * __Coproduct__, @'Monoidal' (->) 'Sum' V1 'Either' 'Data.Void.Void' b@. 'combine'
--   injects a whole record of @f@ or a whole record of @g@ into a record of
--   @'Sum' f g@, all on one side (@'gcombineSum'@); 'introduce' is
--   'Data.Void.absurd'.
--
-- * __Oplax product__ (the @'Op'@ dual of the first), @'Monoidal' 'Op' 'Product' 'Data.Proxy.Proxy' (,) () b@.
--   'combine' unzips a record of 'Data.Functor.Product.Pair's back into two
--   records (@'gsplitProduct'@); 'introduce' is @'Op' ('const' ())@.
--
-- The coproduct has no oplax dual here. A record of independent @'Sum' f g@
-- fields picks a side per field, so there is no single @'Either' (b f) (b g)@ to
-- project back to. The @Divisible@ \/ @Decidable@-style contravariant-functor
-- duals need @f@ in negative position, which is not the @f a@ field shape the
-- generic machinery walks. Neither is provided.
--
-- The generic derivation covers records whose fields all have the shape @f a@.
-- Sums and nested HKD fields are not supported, matching
-- "Data.Functor.Rank2.Traversable".
module Data.Functor.Rank2.Monoidal
  ( -- * Semigroupal
    Semigroupal (..),

    -- * Unital
    Unital (..),

    -- * Monoidal
    Monoidal,

    -- * Generic derivation helpers
    gcombineProduct,
    gsplitProduct,
    gcombineSum,
  )
where

--------------------------------------------------------------------------------

import Data.Either (Either (..), either)
import Data.Function ((.))
import Data.Functor.Product (Product (..))
import Data.Functor.Sum (Sum (..))
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
-- * @cat@ is the codomain category (@Hask@, or 'Op' for the oplax duals).
-- * @t1@ is the domain tensor, acting on functors (e.g. 'Product', 'Sum').
-- * @t0@ is the codomain tensor, acting on @Hask@ (e.g. @(,)@, 'Either').
-- * @b@ is the higher-kinded record.
--
-- The empty-instance default derives the covariant 'Product' instantiation. For
-- the coproduct and oplax-product instantiations, supply @'combine'@ from the
-- exported generic helpers (see 'gcombineSum' and 'gsplitProduct').
type Semigroupal ::
  (Type -> Type -> Type) ->
  ((Type -> Type) -> (Type -> Type) -> (Type -> Type)) ->
  (Type -> Type -> Type) ->
  ((Type -> Type) -> Type) ->
  Constraint
class Semigroupal cat t1 t0 b where
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
  combine = gcombineProduct

--------------------------------------------------------------------------------

-- | The rank-2 analogue of 'Data.Functor.Monoidal.Unital'. A rank-2 functor
-- @b@ is 'Unital' if it carries a morphism from the codomain unit to @b@ at the
-- domain unit, which we call 'introduce'.
--
-- * @cat@ is the codomain category (@Hask@, or 'Op' for the oplax duals).
-- * @i1@ is the domain unit, a functor (the unit of @t1@; 'Proxy' for 'Product',
--   @V1@ for 'Sum').
-- * @i0@ is the codomain unit (the unit of @t0@; @()@ for @(,)@, 'Data.Void.Void'
--   for 'Either').
-- * @b@ is the higher-kinded record.
--
-- The empty-instance default derives the covariant 'Proxy' unit. The coproduct
-- unit is @'introduce' = 'Data.Void.absurd'@ and the oplax-product unit is
-- @'introduce' = 'Op' ('const' ())@; both are trivial enough to write inline.
type Unital ::
  (Type -> Type -> Type) ->
  (Type -> Type) ->
  Type ->
  ((Type -> Type) -> Type) ->
  Constraint
class Unital cat i1 i0 b where
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
-- Generic derivation helpers.

-- | Generic covariant product 'combine': zip two records field-wise into
-- 'Data.Functor.Product.Pair's. This is the default for
-- @'Semigroupal' (->) 'Product' (,)@.
gcombineProduct ::
  ( Generic (b f),
    Generic (b g),
    Generic (b (Product f g)),
    GSemigroupal (Rep (b f)) (Rep (b g)) (Rep (b (Product f g)))
  ) =>
  (b f, b g) ->
  b (Product f g)
gcombineProduct (bf, bg) = to (gcombine (from bf, from bg))

-- | Generic oplax product 'combine': unzip a record of
-- 'Data.Functor.Product.Pair's back into two records. Wrap in 'Op' for
-- @'Semigroupal' 'Op' 'Product' (,)@: @combine = 'Op' 'gsplitProduct'@.
gsplitProduct ::
  ( Generic (b f),
    Generic (b g),
    Generic (b (Product f g)),
    GSemigroupal (Rep (b f)) (Rep (b g)) (Rep (b (Product f g)))
  ) =>
  b (Product f g) ->
  (b f, b g)
gsplitProduct bfg = case gsplit (from bfg) of (l, r) -> (to l, to r)

-- | Generic coproduct 'combine': inject a whole record of @f@ or a whole record
-- of @g@ into a record of @'Sum' f g@, all on one side. This is @combine@ for
-- @'Semigroupal' (->) 'Sum' 'Either'@.
gcombineSum ::
  ( Generic (b f),
    Generic (b g),
    Generic (b (Sum f g)),
    GCoproduct (Rep (b f)) (Rep (b g)) (Rep (b (Sum f g)))
  ) =>
  Either (b f) (b g) ->
  b (Sum f g)
gcombineSum = either (to . ginjectL . from) (to . ginjectR . from)

--------------------------------------------------------------------------------
-- Generic workers for the product tensor (zip and its inverse split).

-- | Generic worker for the 'Product' tensor. The three representations are
-- @'Rep' (b f)@, @'Rep' (b g)@, and @'Rep' (b (Product f g))@; structurally
-- identical up to the field interpretation, which 'gcombine' fuses into a
-- 'Data.Functor.Product.Pair' and 'gsplit' takes apart.
type GSemigroupal :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Constraint
class GSemigroupal repf repg reph where
  gcombine :: (repf x, repg x) -> reph x
  gsplit :: reph x -> (repf x, repg x)

instance (GSemigroupal repf repg reph) => GSemigroupal (M1 i c repf) (M1 i c repg) (M1 i c reph) where
  gcombine (M1 a, M1 b) = M1 (gcombine (a, b))
  gsplit (M1 a) = case gsplit a of (l, r) -> (M1 l, M1 r)

instance (GSemigroupal f1 g1 h1, GSemigroupal f2 g2 h2) => GSemigroupal (f1 :*: f2) (g1 :*: g2) (h1 :*: h2) where
  gcombine (a1 :*: a2, b1 :*: b2) = gcombine (a1, b1) :*: gcombine (a2, b2)
  gsplit (a1 :*: a2) = case (gsplit a1, gsplit a2) of ((l1, r1), (l2, r2)) -> (l1 :*: l2, r1 :*: r2)

instance GSemigroupal (K1 i (p a)) (K1 i (q a)) (K1 i (Product p q a)) where
  gcombine (K1 pa, K1 qa) = K1 (Pair pa qa)
  gsplit (K1 (Pair pa qa)) = (K1 pa, K1 qa)

instance GSemigroupal U1 U1 U1 where
  gcombine (U1, U1) = U1
  gsplit U1 = (U1, U1)

--------------------------------------------------------------------------------
-- Generic worker for the coproduct tensor (all-left \/ all-right injection).

-- | Generic worker for the 'Sum' tensor. 'ginjectL' sends a record of @f@ to a
-- record of @'Sum' f g@ with every field 'InL'; 'ginjectR' does the same with
-- 'InR'.
type GCoproduct :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Constraint
class GCoproduct repf repg reph | reph -> repf repg where
  ginjectL :: repf x -> reph x
  ginjectR :: repg x -> reph x

instance (GCoproduct repf repg reph) => GCoproduct (M1 i c repf) (M1 i c repg) (M1 i c reph) where
  ginjectL (M1 a) = M1 (ginjectL a)
  ginjectR (M1 a) = M1 (ginjectR a)

instance (GCoproduct f1 g1 h1, GCoproduct f2 g2 h2) => GCoproduct (f1 :*: f2) (g1 :*: g2) (h1 :*: h2) where
  ginjectL (a1 :*: a2) = ginjectL a1 :*: ginjectL a2
  ginjectR (a1 :*: a2) = ginjectR a1 :*: ginjectR a2

instance GCoproduct (K1 i (f a)) (K1 i (g a)) (K1 i (Sum f g a)) where
  ginjectL (K1 fa) = K1 (InL fa)
  ginjectR (K1 ga) = K1 (InR ga)

instance GCoproduct U1 U1 U1 where
  ginjectL U1 = U1
  ginjectR U1 = U1

--------------------------------------------------------------------------------
-- Generic worker for the unit (fill every field with the domain unit).

-- | Generic worker for 'introduce' at the covariant 'Proxy' unit: fills every
-- field of @'Rep' (b Proxy)@ with 'Proxy'.
type GUnital :: (Type -> Type) -> Constraint
class GUnital rep where
  gintroduce :: rep x

instance (GUnital rep) => GUnital (M1 i c rep) where
  gintroduce = M1 gintroduce

instance (GUnital f, GUnital g) => GUnital (f :*: g) where
  gintroduce = gintroduce :*: gintroduce

instance GUnital (K1 i (Proxy a)) where
  gintroduce = K1 Proxy

instance GUnital U1 where
  gintroduce = U1
