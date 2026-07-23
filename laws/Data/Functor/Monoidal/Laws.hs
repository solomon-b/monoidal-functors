{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Reusable @hedgehog-classes@ 'Laws' for this library's monoidal-functor
-- classes, so a consumer can law-test their own 'Semigroupal' \/ 'Unital' \/
-- 'Monoidal' instances the same way they test 'Monoid' or 'Applicative':
--
-- > import Data.Functor.Monoidal.Laws (monoidalLaws)
-- > import Hedgehog.Classes (lawsCheck)
-- >
-- > main :: IO Bool
-- > main = lawsCheck (monoidalLaws @(,) @() genMyFunctor)
--
-- The 'Semigroupal' associativity and naturality laws are stated once, point-free
-- and parametric in the category @cat@ ('assocSquare', 'natSquare'). At
-- @cat = (->)@ they give the covariant laws, at @cat = 'Op'@ the colax (split)
-- laws. 'checkCov' and 'checkOp' run the two directions.
--
-- 'semigroupalLaws' \/ 'unitalLaws' \/ 'monoidalLaws' cover the covariant family,
-- general in the codomain tensor @t1@ (and, for units, its unit @i1@). One
-- function handles @(,)@ (Applicative \/ Divisible), @Either@ (Alternative \/
-- Decidable), and @These@ (Semialign). 'opSemigroupalLaws' covers the @'Op'@
-- family, general in @t1@ and the split tensor @t0@. It handles the unzip
-- @f (a, b) -> (f a, f b)@ (@t0 = (,)@), the @Unalign@ split
-- @f ('Data.These.These' a b) -> (f a, f b)@, and
-- @f ('Either' a b) -> 'Either' (f a) (f b)@ (@t0 = 'Either'@).
--
-- The @contravariant*@ family covers contravariant functors (@Divisible@ \/
-- @Decidable@), which lack 'Eq' \/ 'Show'. Each is observed on a generated input
-- through a caller-supplied @obs :: forall a. f a -> a -> r@.
--
-- The rank-2 generator @forall x. 'Gen' x -> 'Gen' (f x)@ instantiates @f@ at the
-- element types each square needs.
module Data.Functor.Monoidal.Laws
  ( -- * Covariant functors
    semigroupalLaws,
    unitalLaws,
    monoidalLaws,

    -- * Contravariant functors
    contravariantSemigroupalLaws,
    contravariantUnitalLaws,
    contravariantMonoidalLaws,

    -- * The Op (comonoidal) laxator
    opSemigroupalLaws,
    representableSplitLaws,
  )
where

--------------------------------------------------------------------------------

import Control.Category ((.))
import Control.Category.Tensor (Associative (..), GBifunctor (gbimap), Iso (..), Tensor (..), glmap, grmap)
import Data.Functor.Contravariant (Contravariant (..), Op (..))
import Data.Functor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import Hedgehog (Gen, Property, forAll, forAllWith, property, (===))
import Hedgehog.Classes (Laws (..))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude hiding ((.))

--------------------------------------------------------------------------------

-- | The element type the coherence squares are witnessed at.
genInt :: Gen Int
genInt = Gen.int (Range.linear (-100) 100)

genPair :: Gen a -> Gen b -> Gen (a, b)
genPair ga gb = (,) <$> ga <*> gb

--------------------------------------------------------------------------------
-- Cat-parametric coherence squares.
--
-- The associativity and naturality squares are stated once at an abstract
-- category @cat@. At @cat = (->)@ they are the covariant laws. At @cat = 'Op'@
-- they are the colax (split) laws, since @'bwd' ('assoc' \@'Op') = 'Op' ('fwd'
-- 'assoc')@. 'checkCov' and 'checkOp' run the two directions.

-- | The two parallel @cat@-morphisms a coherence law asserts equal.
data Square cat s t = Square (cat s t) (cat s t)

-- | Lift a @cat@-morphism through @f@. @'fmap'@ at @(->)@, @'fmap'@ under
-- arrow-reversal at @'Op'@.
class MapF cat f where
  mapF :: cat a b -> cat (f a) (f b)

instance (Functor f) => MapF (->) f where
  mapF = fmap

instance (Functor f) => MapF Op f where
  mapF (Op g) = Op (fmap g)

-- | Associativity of the laxator. @'combine'@ commutes with the domain and
-- codomain associators. This is the coherence square documented on 'Semigroupal'.
assocSquare ::
  forall cat t1 t0 f a b c.
  ( Semigroupal cat t1 t0 f,
    Associative cat t0,
    Associative cat t1,
    MapF cat f
  ) =>
  Square cat (t0 (t0 (f a) (f b)) (f c)) (f (t1 a (t1 b c)))
assocSquare =
  Square
    (combine @cat @t1 @t0 . grmap (combine @cat @t1 @t0) . bwd (assoc @cat @t0))
    (mapF (bwd (assoc @cat @t1)) . combine @cat @t1 @t0 . glmap (combine @cat @t1 @t0))

-- | Naturality of the laxator. @'combine'@ commutes with maps into either tensor.
natSquare ::
  forall cat t1 t0 f a a' b b'.
  ( Semigroupal cat t1 t0 f,
    Associative cat t0,
    Associative cat t1,
    MapF cat f
  ) =>
  cat a a' ->
  cat b b' ->
  Square cat (t0 (f a) (f b)) (f (t1 a' b'))
natSquare g h =
  Square
    (mapF (gbimap @cat @cat @cat @t1 g h) . combine @cat @t1 @t0)
    (combine @cat @t1 @t0 . gbimap @cat @cat @cat @t0 (mapF g) (mapF h))

-- | Run a covariant square. Apply each side to a generated source, compare with
-- 'Eq'.
checkCov ::
  forall s t.
  (Eq t, Show s, Show t) =>
  Gen s ->
  Square (->) s t ->
  Property
checkCov gen (Square l r) = property $ do
  s <- forAll gen
  l s === r s

-- | Run an @'Op'@ square. Each side unwraps to a split @t -> s@. Generate the
-- input at @t@, compare the outputs at @s@.
checkOp ::
  forall s t.
  (Eq s, Show s, Show t) =>
  Gen t ->
  Square Op s t ->
  Property
checkOp gen (Square (Op l) (Op r)) = property $ do
  t <- forAll gen
  l t === r t

--------------------------------------------------------------------------------

-- | 'combine' laws. It commutes with the codomain tensor's associator
-- (associativity) and with maps into it (naturality of the laxator).
semigroupalLaws ::
  forall t1 f.
  ( Semigroupal (->) t1 (,) f,
    Associative (->) t1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
semigroupalLaws genF =
  Laws
    "Semigroupal"
    [ ("Associativity", semigroupalAssoc @t1 genF),
      ("Naturality", semigroupalNaturality @t1 genF)
    ]

semigroupalNaturality ::
  forall t1 f.
  ( Semigroupal (->) t1 (,) f,
    Associative (->) t1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
semigroupalNaturality genF =
  checkCov
    (genPair (genF genInt) (genF genInt))
    (natSquare @(->) @t1 @(,) ((+ 1) :: Int -> Int) ((* 2) :: Int -> Int))

semigroupalAssoc ::
  forall t1 f.
  ( Semigroupal (->) t1 (,) f,
    Associative (->) t1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
semigroupalAssoc genF =
  checkCov
    (genPair (genPair (genF genInt) (genF genInt)) (genF genInt))
    (assocSquare @(->) @t1 @(,))

--------------------------------------------------------------------------------

-- | Left and right unit laws. 'introduce' is a unit for 'combine', up to the
-- codomain tensor's unitors.
unitalLaws ::
  forall t1 i1 f.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Tensor (->) t1 i1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
unitalLaws genF =
  Laws
    "Unital"
    [ ("Left Unit", unitalLeft @t1 @i1 genF),
      ("Right Unit", unitalRight @t1 @i1 genF)
    ]

unitalLeft ::
  forall t1 i1 f.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Tensor (->) t1 i1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
unitalLeft genF = property $ do
  fa <- forAll (genF genInt)
  fmap (fwd (unitl @(->) @t1)) (combine @(->) @t1 @(,) (introduce @(->) @i1 @() (), fa)) === fa

unitalRight ::
  forall t1 i1 f.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Tensor (->) t1 i1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
unitalRight genF = property $ do
  fa <- forAll (genF genInt)
  fmap (fwd (unitr @(->) @t1)) (combine @(->) @t1 @(,) (fa, introduce @(->) @i1 @() ())) === fa

--------------------------------------------------------------------------------

-- | Every 'semigroupalLaws' and 'unitalLaws' property together, for a full
-- 'Monoidal' instance.
monoidalLaws ::
  forall t1 i1 f.
  ( Monoidal (->) t1 i1 (,) () f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
monoidalLaws genF =
  Laws
    "Monoidal"
    ( lawsProperties (semigroupalLaws @t1 genF)
        <> lawsProperties (unitalLaws @t1 @i1 genF)
    )

--------------------------------------------------------------------------------

-- | Laws for the /Op/ (comonoidal) laxator @'combine' \@'Op'@, the split
-- @f (a \`t1\` b) -> t0 (f a) (f b)@. General in the codomain tensor @t1@ and the
-- split tensor @t0@. It builds the same 'assocSquare' \/ 'natSquare' as
-- 'semigroupalLaws' and runs them through 'checkOp'. One function covers every
-- shipped @'Op'@ 'Semigroupal' instance. The unzip @f (a, b) -> (f a, f b)@
-- (@t0 = (,)@), the @Unalign@ split @f ('Data.These.These' a b) -> (f a, f b)@,
-- and @f ('Either' a b) -> 'Either' (f a) (f b)@ (@t0 = 'Either'@). @genT@ builds
-- the @t1@-shaped payloads the split consumes. Covariant functors only.
opSemigroupalLaws ::
  forall t1 t0 f.
  ( Semigroupal Op t1 t0 f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t0 a b),
    forall a b. (Show a, Show b) => Show (t0 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  Laws
opSemigroupalLaws genF genT =
  Laws
    "Semigroupal (Op)"
    [ ("Coassociativity", opCoassoc @t1 @t0 genF genT),
      ("Conaturality", opConaturality @t1 @t0 genF genT)
    ]

opCoassoc ::
  forall t1 t0 f.
  ( Semigroupal Op t1 t0 f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t0 a b),
    forall a b. (Show a, Show b) => Show (t0 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  Property
opCoassoc genF genT =
  checkOp
    (genF (genT genInt (genT genInt genInt)))
    (assocSquare @Op @t1 @t0)

opConaturality ::
  forall t1 t0 f.
  ( Semigroupal Op t1 t0 f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t0 a b),
    forall a b. (Show a, Show b) => Show (t0 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  Property
opConaturality genF genT =
  checkOp
    (genF (genT genInt genInt))
    (natSquare @Op @t1 @t0 (Op ((+ 1) :: Int -> Int)) (Op ((* 2) :: Int -> Int)))

--------------------------------------------------------------------------------

-- | Coherence between the covariant @'combine'@ and the @'Op'@ split. They are
-- mutually inverse. This holds when the split inverts the product @combine@, for
-- representable functors (those deriving via @FromRepresentable@). It is /not/
-- satisfied by the standalone @FromGeneric@ unzip on a non-representable functor,
-- whose cartesian @combine@ the unzip does not invert.
representableSplitLaws ::
  forall f.
  ( Semigroupal (->) (,) (,) f,
    Semigroupal Op (,) (,) f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
representableSplitLaws genF =
  Laws
    "Semigroupal (Op) coherence"
    [ ("split . combine", splitAfterCombine genF),
      ("combine . split", combineAfterSplit genF)
    ]

splitAfterCombine ::
  forall f.
  ( Semigroupal (->) (,) (,) f,
    Semigroupal Op (,) (,) f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
splitAfterCombine genF = property $ do
  x <- forAll (genF genInt)
  y <- forAll (genF genInt)
  getOp (combine @Op @(,) @(,)) (combine @(->) @(,) @(,) (x, y)) === (x, y)

combineAfterSplit ::
  forall f.
  ( Semigroupal (->) (,) (,) f,
    Semigroupal Op (,) (,) f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
combineAfterSplit genF = property $ do
  xy <- forAll (genF (genPair genInt genInt))
  combine @(->) @(,) @(,) (getOp (combine @Op @(,) @(,)) xy) === xy

--------------------------------------------------------------------------------

-- | 'combine' laws for a /contravariant/ functor. Associativity and naturality
-- of the laxator. Since contravariant functors (@Divisible@, @Decidable@)
-- generally are not 'Eq' \/ 'Show', the two sides are observed through @obs@ on
-- a generated element of the codomain tensor. @genT@ is a tensor builder, such as
-- @\\ga gb -> (,) '<$>' ga '<*>' gb@ for @(,)@, or
-- @\\ga gb -> 'Gen.choice' [Left '<$>' ga, Right '<$>' gb]@ for @Either@. It
-- assembles the associativity and naturality observation points.
contravariantSemigroupalLaws ::
  forall t1 f r.
  ( Semigroupal (->) t1 (,) f,
    Contravariant f,
    Associative (->) t1,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  (forall a. f a -> a -> r) ->
  Laws
contravariantSemigroupalLaws genF genT obs =
  Laws
    "Semigroupal"
    [ ("Associativity", contravariantAssoc @t1 genF genT obs),
      ("Naturality", contravariantNaturality @t1 genF genT obs)
    ]

contravariantAssoc ::
  forall t1 f r.
  ( Semigroupal (->) t1 (,) f,
    Contravariant f,
    Associative (->) t1,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantAssoc genF genT obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  y <- forAllWith (const "<opaque>") genF
  z <- forAllWith (const "<opaque>") genF
  t <- forAll (genT genInt (genT genInt genInt))
  obs (contramap (fwd (assoc @(->) @t1)) (combine @(->) @t1 @(,) (combine @(->) @t1 @(,) (x, y), z))) t
    === obs (combine @(->) @t1 @(,) (x, combine @(->) @t1 @(,) (y, z))) t

contravariantNaturality ::
  forall t1 f r.
  ( Semigroupal (->) t1 (,) f,
    Contravariant f,
    Associative (->) t1,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantNaturality genF genT obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  y <- forAllWith (const "<opaque>") genF
  t <- forAll (genT genInt genInt)
  let g = (+ 1) :: Int -> Int
      h = (* 2) :: Int -> Int
  obs (contramap (gbimap @(->) @(->) @(->) @t1 g h) (combine @(->) @t1 @(,) (x, y))) t
    === obs (combine @(->) @t1 @(,) (contramap g x, contramap h y)) t

-- | Left and right unit laws for a /contravariant/ functor, observed through
-- @obs@ at a generated element. The unit laws need no tensor-shaped input.
contravariantUnitalLaws ::
  forall t1 i1 f r.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Contravariant f,
    Tensor (->) t1 i1,
    Eq r,
    Show r
  ) =>
  Gen (f Int) ->
  (forall a. f a -> a -> r) ->
  Laws
contravariantUnitalLaws genF obs =
  Laws
    "Unital"
    [ ("Left Unit", contravariantUnitL @t1 @i1 genF obs),
      ("Right Unit", contravariantUnitR @t1 @i1 genF obs)
    ]

contravariantUnitL ::
  forall t1 i1 f r.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Contravariant f,
    Tensor (->) t1 i1,
    Eq r,
    Show r
  ) =>
  Gen (f Int) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantUnitL genF obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  a <- forAll genInt
  obs (contramap (bwd (unitl @(->) @t1)) (combine @(->) @t1 @(,) (introduce @(->) @i1 @() (), x))) a
    === obs x a

contravariantUnitR ::
  forall t1 i1 f r.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Contravariant f,
    Tensor (->) t1 i1,
    Eq r,
    Show r
  ) =>
  Gen (f Int) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantUnitR genF obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  a <- forAll genInt
  obs (contramap (bwd (unitr @(->) @t1)) (combine @(->) @t1 @(,) (x, introduce @(->) @i1 @() ()))) a
    === obs x a

-- | Every 'contravariantSemigroupalLaws' and 'contravariantUnitalLaws' property
-- together, for a full contravariant 'Monoidal' instance.
contravariantMonoidalLaws ::
  forall t1 i1 f r.
  ( Monoidal (->) t1 i1 (,) () f,
    Contravariant f,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  (forall a. f a -> a -> r) ->
  Laws
contravariantMonoidalLaws genF genT obs =
  Laws
    "Monoidal"
    ( lawsProperties (contravariantSemigroupalLaws @t1 genF genT obs)
        <> lawsProperties (contravariantUnitalLaws @t1 @i1 genF obs)
    )
