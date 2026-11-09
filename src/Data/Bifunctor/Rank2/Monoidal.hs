{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

-- | Rank-2 monoidal bifunctors: the analogue of "Data.Functor.Rank2.Monoidal"
-- for higher-kinded data interpreted by a bifunctor,
-- @b :: (Type -> Type -> Type) -> Type@.
--
-- A rank-2 bifunctor is a functor \(B : [\mathcal{Hask}^{2}, \mathcal{Hask}] \to \mathcal{Hask}\)
-- from the bifunctor category to @Hask@. @b p@ reinterprets each field of the
-- record @b@ through @p@, so the fields have the shape @p a b@ as in
-- "Data.Bifunctor.Rank2.Traversable". "Kindly.Rank2" already supplies the
-- functorial action. This module adds the /monoidal/ structure on top of it.
--
-- The classes take a single domain tensor, like their
-- "Data.Functor.Rank2.Monoidal" siblings and unlike "Data.Bifunctor.Monoidal".
-- A bifunctor's domain is a product category \(\mathcal{C_1} \times \mathcal{C_2}\),
-- so a tensor on it is a pair of tensors, which is why
-- 'Data.Bifunctor.Monoidal.Semigroupal' carries both @t1@ and @t2@. The
-- bifunctor category is one category, so a rank-2 bifunctor needs only one
-- tensor. The extra arity shows up in the tensors themselves
-- ('Data.Bifunctor.Product.Product' rather than 'Data.Functor.Product.Product')
-- and in the field shape, not in the class parameters.
--
-- A product-shaped record is monoidal at three instantiations, all derivable
-- from the record's 'GHC.Generics' structure:
--
-- * __Covariant product__, @'Monoidal' (->) 'Product' ('Joker' 'Data.Proxy.Proxy') (,) () b@.
--   'combine' zips two records field-wise into 'Data.Bifunctor.Product.Pair's and
--   'introduce' fills every field with the unit bifunctor.
--
-- * __Coproduct__, @'Monoidal' (->) 'Sum' ('Joker' V1) 'Either' 'Data.Void.Void' b@.
--   'combine' injects a whole record of @p@ or a whole record of @q@ into a record
--   of @'Sum' p q@, all on one side (@'gcombineSum'@). 'introduce' is
--   'Data.Void.absurd'.
--
-- * __Oplax product__ (the @'Op'@ dual of the first), @'Monoidal' 'Op' 'Product' ('Joker' 'Data.Proxy.Proxy') (,) () b@.
--   'combine' unzips a record of 'Data.Bifunctor.Product.Pair's back into two
--   records (@'gsplitProduct'@). 'introduce' is @'Op' ('const' ())@.
--
-- The tensor units are spelled with 'Joker' because @bifunctors@ ships no unit
-- or empty bifunctor of its own. @'Joker' 'Data.Proxy.Proxy'@ is the bifunctor
-- constant at @()@ (the unit of 'Product') and @'Joker' V1@ is the empty
-- bifunctor (the unit of 'Sum'). The latter is a phantom, since
-- @'introduce' = 'Data.Void.absurd'@ never builds a value at it.
--
-- The coproduct has no oplax dual here. A record of independent @'Sum' p q@
-- fields picks per field, so there is no single @'Either' (b p) (b q)@ to
-- project back to. There is also no @These@ instantiation, because the ecosystem
-- has no bifunctor analogue of 'Data.Functor.These.These1'. The @Divisible@ \/
-- @Decidable@-style duals need the interpretation in negative position, which is
-- not the @p a b@ field shape the generic machinery walks.
--
-- The generic derivation covers records whose fields all have the shape @p a b@.
-- Sums and nested HKD fields are not supported, matching
-- "Data.Bifunctor.Rank2.Traversable".
module Data.Bifunctor.Rank2.Monoidal
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

import Data.Bifunctor.Joker (Joker (..))
import Data.Bifunctor.Product (Product (..))
import Data.Bifunctor.Sum (Sum (..))
import Data.Either (Either (..), either)
import Data.Function ((.))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
#if MIN_VERSION_base(4,17,0)
-- On GHC 9.4+ (@base >= 4.17@) @~@ is an ordinary type operator rather than
-- built-in syntax, so under @NoImplicitPrelude@ it must be brought into scope.
-- Earlier GHCs still treat @~@ as built-in syntax and do not export it.
import Data.Type.Equality (type (~))
#endif
import GHC.Generics (Generic (..), K1 (..), M1 (..), U1 (..), type (:*:) (..))

--------------------------------------------------------------------------------

-- $setup
-- >>> :set -XDeriveGeneric -XStandaloneDeriving -XFlexibleContexts -XMultiParamTypeClasses -XTypeApplications
-- >>> import Prelude
-- >>> import GHC.Generics (Generic)
-- >>> import Data.Bifunctor.Joker (Joker (..))
-- >>> import Data.Bifunctor.Product (Product (..))
-- >>> import Data.Bifunctor.Sum (Sum (..))
-- >>> import Data.Proxy (Proxy (..))
-- >>> :{
-- data Rec p = Rec {rFst :: p Int Bool, rSnd :: p String Int} deriving Generic
-- deriving instance (Show (p Int Bool), Show (p String Int)) => Show (Rec p)
-- instance Semigroupal (->) Product (,) Rec
-- instance Unital (->) (Joker Proxy) () Rec
-- instance Monoidal (->) Product (Joker Proxy) (,) () Rec
-- instance Semigroupal (->) Sum Either Rec where combine = gcombineSum
-- :}

--------------------------------------------------------------------------------

-- | The rank-2 analogue of 'Data.Bifunctor.Monoidal.Semigroupal'. Given a
-- monoidal structure \(\otimes\) on the bifunctor category and \(\bullet\) on
-- @Hask@, a rank-2 bifunctor @b@ is 'Semigroupal' if it carries a natural
-- transformation \(\phi_{p,q} : b\ p \bullet b\ q \to b\ (p \otimes q)\), which
-- we call 'combine'.
--
-- * @cat@ is the codomain category (@Hask@, or 'Op' for the oplax dual).
-- * @t1@ is the domain tensor, acting on bifunctors (e.g. 'Product', 'Sum').
-- * @t0@ is the codomain tensor, acting on @Hask@ (e.g. @(,)@, 'Either').
-- * @b@ is the higher-kinded record.
--
-- The empty-instance default derives the covariant 'Product' instantiation. For
-- the coproduct and oplax-product instantiations, supply @'combine'@ from the
-- exported generic helpers (see 'gcombineSum' and 'gsplitProduct').
type Semigroupal ::
  (Type -> Type -> Type) ->
  ((Type -> Type -> Type) -> (Type -> Type -> Type) -> (Type -> Type -> Type)) ->
  (Type -> Type -> Type) ->
  ((Type -> Type -> Type) -> Type) ->
  Constraint
class Semigroupal cat t1 t0 b where
  -- | ==== __Examples__
  --
  -- Zip two records field-wise (the covariant 'Product' instantiation):
  --
  -- >>> combine @(->) @Product @(,) (Rec (1, True) ("hi", 2) :: Rec (,), Rec (Left 3) (Right 4) :: Rec Either)
  -- Rec {rFst = Pair (1,True) (Left 3), rSnd = Pair ("hi",2) (Right 4)}
  --
  -- Inject a whole record onto one side of a 'Sum' (the coproduct instantiation):
  --
  -- >>> combine @(->) @Sum @Either (Left (Rec (1, True) ("hi", 2)) :: Either (Rec (,)) (Rec Either))
  -- Rec {rFst = L2 (1,True), rSnd = L2 ("hi",2)}
  combine :: forall p q. cat (t0 (b p) (b q)) (b (t1 p q))
  default combine ::
    forall p q.
    ( cat ~ (->),
      t1 ~ Product,
      t0 ~ (,),
      Generic (b p),
      Generic (b q),
      Generic (b (Product p q)),
      GSemigroupal (Rep (b p)) (Rep (b q)) (Rep (b (Product p q)))
    ) =>
    cat (t0 (b p) (b q)) (b (t1 p q))
  combine = gcombineProduct

--------------------------------------------------------------------------------

-- | The rank-2 analogue of 'Data.Bifunctor.Monoidal.Unital'. A rank-2 bifunctor
-- @b@ is 'Unital' if it carries a morphism from the codomain unit to @b@ at the
-- domain unit, which we call 'introduce'.
--
-- * @cat@ is the codomain category (@Hask@, or 'Op' for the oplax dual).
-- * @i1@ is the domain unit, a bifunctor (the unit of @t1@;
--   @'Joker' 'Data.Proxy.Proxy'@ for 'Product', @'Joker' V1@ for 'Sum').
-- * @i0@ is the codomain unit (the unit of @t0@; @()@ for @(,)@, 'Data.Void.Void'
--   for 'Either').
-- * @b@ is the higher-kinded record.
--
-- The empty-instance default derives the covariant @'Joker' 'Data.Proxy.Proxy'@
-- unit. The coproduct unit is @'introduce' = 'Data.Void.absurd'@ and the
-- oplax-product unit is @'introduce' = 'Op' ('const' ())@. Both are trivial
-- enough to write inline.
type Unital ::
  (Type -> Type -> Type) ->
  (Type -> Type -> Type) ->
  Type ->
  ((Type -> Type -> Type) -> Type) ->
  Constraint
class Unital cat i1 i0 b where
  -- | ==== __Examples__
  --
  -- >>> introduce @(->) @(Joker Proxy) @() @Rec ()
  -- Rec {rFst = Joker {runJoker = Proxy}, rSnd = Joker {runJoker = Proxy}}
  introduce :: cat i0 (b i1)
  default introduce ::
    ( cat ~ (->),
      i1 ~ Joker Proxy,
      i0 ~ (),
      Generic (b (Joker Proxy)),
      GUnital (Rep (b (Joker Proxy)))
    ) =>
    cat i0 (b i1)
  introduce () = to gintroduce

--------------------------------------------------------------------------------

-- | The rank-2 analogue of 'Data.Bifunctor.Monoidal.Monoidal'. A rank-2
-- bifunctor that is both 'Semigroupal' and 'Unital', preserving the monoidal
-- structure between the bifunctor category and @Hask@.
type Monoidal ::
  (Type -> Type -> Type) ->
  ((Type -> Type -> Type) -> (Type -> Type -> Type) -> (Type -> Type -> Type)) ->
  (Type -> Type -> Type) ->
  (Type -> Type -> Type) ->
  Type ->
  ((Type -> Type -> Type) -> Type) ->
  Constraint
class
  ( Semigroupal cat t1 t0 b,
    Unital cat i1 i0 b
  ) =>
  Monoidal cat t1 i1 t0 i0 b

--------------------------------------------------------------------------------
-- Generic derivation helpers.

-- | Generic covariant product 'combine': zip two records field-wise into
-- 'Data.Bifunctor.Product.Pair's. This is the default for
-- @'Semigroupal' (->) 'Product' (,)@.
--
-- ==== __Examples__
--
-- >>> gcombineProduct (Rec (1, True) ("hi", 2) :: Rec (,), Rec (Left 3) (Right 4) :: Rec Either)
-- Rec {rFst = Pair (1,True) (Left 3), rSnd = Pair ("hi",2) (Right 4)}
gcombineProduct ::
  ( Generic (b p),
    Generic (b q),
    Generic (b (Product p q)),
    GSemigroupal (Rep (b p)) (Rep (b q)) (Rep (b (Product p q)))
  ) =>
  (b p, b q) ->
  b (Product p q)
gcombineProduct (bp, bq) = to (gcombine (from bp, from bq))

-- | Generic oplax product 'combine': unzip a record of
-- 'Data.Bifunctor.Product.Pair's back into two records. Wrap in 'Op' for
-- @'Semigroupal' 'Op' 'Product' (,)@: @combine = 'Op' 'gsplitProduct'@.
--
-- ==== __Examples__
--
-- >>> gsplitProduct (Rec (Pair (1, True) (Left 3)) (Pair ("hi", 2) (Right 4)))
-- (Rec {rFst = (1,True), rSnd = ("hi",2)},Rec {rFst = Left 3, rSnd = Right 4})
gsplitProduct ::
  ( Generic (b p),
    Generic (b q),
    Generic (b (Product p q)),
    GSemigroupal (Rep (b p)) (Rep (b q)) (Rep (b (Product p q)))
  ) =>
  b (Product p q) ->
  (b p, b q)
gsplitProduct bpq = case gsplit (from bpq) of (l, r) -> (to l, to r)

-- | Generic coproduct 'combine': inject a whole record of @p@ or a whole record
-- of @q@ into a record of @'Sum' p q@, all on one side. This is @combine@ for
-- @'Semigroupal' (->) 'Sum' 'Either'@.
--
-- ==== __Examples__
--
-- >>> gcombineSum (Right (Rec (Left 3) (Right 4)) :: Either (Rec (,)) (Rec Either))
-- Rec {rFst = R2 (Left 3), rSnd = R2 (Right 4)}
gcombineSum ::
  ( Generic (b p),
    Generic (b q),
    Generic (b (Sum p q)),
    GCoproduct (Rep (b p)) (Rep (b q)) (Rep (b (Sum p q)))
  ) =>
  Either (b p) (b q) ->
  b (Sum p q)
gcombineSum = either (to . ginjectL . from) (to . ginjectR . from)

--------------------------------------------------------------------------------
-- Generic workers for the product tensor (zip and its inverse split).

-- | Generic worker for the 'Product' tensor. The three representations are
-- @'Rep' (b p)@, @'Rep' (b q)@, and @'Rep' (b (Product p q))@. They are
-- structurally identical up to the field interpretation, which 'gcombine' fuses
-- into a 'Data.Bifunctor.Product.Pair' and 'gsplit' takes apart.
type GSemigroupal :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Constraint
class GSemigroupal repp repq reph where
  gcombine :: (repp x, repq x) -> reph x
  gsplit :: reph x -> (repp x, repq x)

instance (GSemigroupal repp repq reph) => GSemigroupal (M1 i c repp) (M1 i c repq) (M1 i c reph) where
  gcombine (M1 a, M1 b) = M1 (gcombine (a, b))
  gsplit (M1 a) = case gsplit a of (l, r) -> (M1 l, M1 r)

instance (GSemigroupal p1 q1 h1, GSemigroupal p2 q2 h2) => GSemigroupal (p1 :*: p2) (q1 :*: q2) (h1 :*: h2) where
  gcombine (a1 :*: a2, b1 :*: b2) = gcombine (a1, b1) :*: gcombine (a2, b2)
  gsplit (a1 :*: a2) = case (gsplit a1, gsplit a2) of ((l1, r1), (l2, r2)) -> (l1 :*: l2, r1 :*: r2)

instance GSemigroupal (K1 i (p a b)) (K1 i (q a b)) (K1 i (Product p q a b)) where
  gcombine (K1 pab, K1 qab) = K1 (Pair pab qab)
  gsplit (K1 (Pair pab qab)) = (K1 pab, K1 qab)

instance GSemigroupal U1 U1 U1 where
  gcombine (U1, U1) = U1
  gsplit U1 = (U1, U1)

--------------------------------------------------------------------------------
-- Generic worker for the coproduct tensor (all-left \/ all-right injection).

-- | Generic worker for the 'Sum' tensor. 'ginjectL' sends a record of @p@ to a
-- record of @'Sum' p q@ with every field 'L2'. 'ginjectR' does the same with
-- 'R2'.
type GCoproduct :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Constraint
class GCoproduct repp repq reph | reph -> repp repq where
  ginjectL :: repp x -> reph x
  ginjectR :: repq x -> reph x

instance (GCoproduct repp repq reph) => GCoproduct (M1 i c repp) (M1 i c repq) (M1 i c reph) where
  ginjectL (M1 a) = M1 (ginjectL a)
  ginjectR (M1 a) = M1 (ginjectR a)

instance (GCoproduct p1 q1 h1, GCoproduct p2 q2 h2) => GCoproduct (p1 :*: p2) (q1 :*: q2) (h1 :*: h2) where
  ginjectL (a1 :*: a2) = ginjectL a1 :*: ginjectL a2
  ginjectR (a1 :*: a2) = ginjectR a1 :*: ginjectR a2

instance GCoproduct (K1 i (p a b)) (K1 i (q a b)) (K1 i (Sum p q a b)) where
  ginjectL (K1 pab) = K1 (L2 pab)
  ginjectR (K1 qab) = K1 (R2 qab)

instance GCoproduct U1 U1 U1 where
  ginjectL U1 = U1
  ginjectR U1 = U1

--------------------------------------------------------------------------------
-- Generic worker for the unit (fill every field with the domain unit).

-- | Generic worker for 'introduce' at the covariant @'Joker' 'Data.Proxy.Proxy'@
-- unit. Fills every field of @'Rep' (b ('Joker' 'Data.Proxy.Proxy'))@ with the
-- unit bifunctor.
type GUnital :: (Type -> Type) -> Constraint
class GUnital rep where
  gintroduce :: rep x

instance (GUnital rep) => GUnital (M1 i c rep) where
  gintroduce = M1 gintroduce

instance (GUnital p, GUnital q) => GUnital (p :*: q) where
  gintroduce = gintroduce :*: gintroduce

instance GUnital (K1 i (Joker Proxy a b)) where
  gintroduce = K1 (Joker Proxy)

instance GUnital U1 where
  gintroduce = U1
