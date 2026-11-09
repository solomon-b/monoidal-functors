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
-- general in the domain tensor @tC@ (and, for units, its unit @iC@). One
-- function handles @(,)@ (Applicative \/ Divisible), @Either@ (Alternative \/
-- Decidable), and @These@ (Semialign). 'opSemigroupalLaws' covers the @'Op'@
-- family, general in @tC@ and the split tensor @tD@. It handles the unzip
-- @f (a, b) -> (f a, f b)@ (@tD = (,)@), the @Unalign@ split
-- @f ('Data.These.These' a b) -> (f a, f b)@, and
-- @f ('Either' a b) -> 'Either' (f a) (f b)@ (@tD = 'Either'@).
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
  forall cat tC tD f a b c.
  ( Semigroupal cat tC tD f,
    Associative cat tD,
    Associative cat tC,
    MapF cat f
  ) =>
  Square cat (tD (tD (f a) (f b)) (f c)) (f (tC a (tC b c)))
assocSquare =
  Square
    (combine @cat @tC @tD . grmap (combine @cat @tC @tD) . bwd (assoc @cat @tD))
    (mapF (bwd (assoc @cat @tC)) . combine @cat @tC @tD . glmap (combine @cat @tC @tD))

-- | Naturality of the laxator. @'combine'@ commutes with maps into either tensor.
natSquare ::
  forall cat tC tD f a a' b b'.
  ( Semigroupal cat tC tD f,
    Associative cat tD,
    Associative cat tC,
    MapF cat f
  ) =>
  cat a a' ->
  cat b b' ->
  Square cat (tD (f a) (f b)) (f (tC a' b'))
natSquare g h =
  Square
    (mapF (gbimap @cat @cat @cat @tC g h) . combine @cat @tC @tD)
    (combine @cat @tC @tD . gbimap @cat @cat @cat @tD (mapF g) (mapF h))

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
  forall tC f.
  ( Semigroupal (->) tC (,) f,
    Associative (->) tC,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (tC a b),
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
semigroupalLaws genF =
  Laws
    "Semigroupal"
    [ ("Associativity", semigroupalAssoc @tC genF),
      ("Naturality", semigroupalNaturality @tC genF)
    ]

semigroupalNaturality ::
  forall tC f.
  ( Semigroupal (->) tC (,) f,
    Associative (->) tC,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (tC a b),
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
semigroupalNaturality genF =
  checkCov
    (genPair (genF genInt) (genF genInt))
    (natSquare @(->) @tC @(,) ((+ 1) :: Int -> Int) ((* 2) :: Int -> Int))

semigroupalAssoc ::
  forall tC f.
  ( Semigroupal (->) tC (,) f,
    Associative (->) tC,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (tC a b),
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
semigroupalAssoc genF =
  checkCov
    (genPair (genPair (genF genInt) (genF genInt)) (genF genInt))
    (assocSquare @(->) @tC @(,))

--------------------------------------------------------------------------------

-- | Left and right unit laws. 'introduce' is a unit for 'combine', up to the
-- codomain tensor's unitors.
unitalLaws ::
  forall tC iC f.
  ( Semigroupal (->) tC (,) f,
    Unital (->) iC () f,
    Tensor (->) tC iC,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
unitalLaws genF =
  Laws
    "Unital"
    [ ("Left Unit", unitalLeft @tC @iC genF),
      ("Right Unit", unitalRight @tC @iC genF)
    ]

unitalLeft ::
  forall tC iC f.
  ( Semigroupal (->) tC (,) f,
    Unital (->) iC () f,
    Tensor (->) tC iC,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
unitalLeft genF = property $ do
  fa <- forAll (genF genInt)
  fmap (fwd (unitl @(->) @tC)) (combine @(->) @tC @(,) (introduce @(->) @iC @() (), fa)) === fa

unitalRight ::
  forall tC iC f.
  ( Semigroupal (->) tC (,) f,
    Unital (->) iC () f,
    Tensor (->) tC iC,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
unitalRight genF = property $ do
  fa <- forAll (genF genInt)
  fmap (fwd (unitr @(->) @tC)) (combine @(->) @tC @(,) (fa, introduce @(->) @iC @() ())) === fa

--------------------------------------------------------------------------------

-- | Every 'semigroupalLaws' and 'unitalLaws' property together, for a full
-- 'Monoidal' instance.
monoidalLaws ::
  forall tC iC f.
  ( Monoidal (->) tC iC (,) () f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (tC a b),
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
monoidalLaws genF =
  Laws
    "Monoidal"
    ( lawsProperties (semigroupalLaws @tC genF)
        <> lawsProperties (unitalLaws @tC @iC genF)
    )

--------------------------------------------------------------------------------

-- | Laws for the /Op/ (comonoidal) laxator @'combine' \@'Op'@, the split
-- @f (a \`tC\` b) -> tD (f a) (f b)@. General in the domain tensor @tC@ and the
-- split tensor @tD@. It builds the same 'assocSquare' \/ 'natSquare' as
-- 'semigroupalLaws' and runs them through 'checkOp'. One function covers every
-- shipped @'Op'@ 'Semigroupal' instance. The unzip @f (a, b) -> (f a, f b)@
-- (@tD = (,)@), the @Unalign@ split @f ('Data.These.These' a b) -> (f a, f b)@,
-- and @f ('Either' a b) -> 'Either' (f a) (f b)@ (@tD = 'Either'@). @genT@ builds
-- the @tC@-shaped payloads the split consumes. Covariant functors only.
opSemigroupalLaws ::
  forall tC tD f.
  ( Semigroupal Op tC tD f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (tD a b),
    forall a b. (Show a, Show b) => Show (tD a b),
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  (forall a b. Gen a -> Gen b -> Gen (tC a b)) ->
  Laws
opSemigroupalLaws genF genT =
  Laws
    "Semigroupal (Op)"
    [ ("Coassociativity", opCoassoc @tC @tD genF genT),
      ("Conaturality", opConaturality @tC @tD genF genT)
    ]

opCoassoc ::
  forall tC tD f.
  ( Semigroupal Op tC tD f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (tD a b),
    forall a b. (Show a, Show b) => Show (tD a b),
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  (forall a b. Gen a -> Gen b -> Gen (tC a b)) ->
  Property
opCoassoc genF genT =
  checkOp
    (genF (genT genInt (genT genInt genInt)))
    (assocSquare @Op @tC @tD)

opConaturality ::
  forall tC tD f.
  ( Semigroupal Op tC tD f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (tD a b),
    forall a b. (Show a, Show b) => Show (tD a b),
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  (forall a b. Gen a -> Gen b -> Gen (tC a b)) ->
  Property
opConaturality genF genT =
  checkOp
    (genF (genT genInt genInt))
    (natSquare @Op @tC @tD (Op ((+ 1) :: Int -> Int)) (Op ((* 2) :: Int -> Int)))

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
  forall tC f r.
  ( Semigroupal (->) tC (,) f,
    Contravariant f,
    Associative (->) tC,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (tC a b)) ->
  (forall a. f a -> a -> r) ->
  Laws
contravariantSemigroupalLaws genF genT obs =
  Laws
    "Semigroupal"
    [ ("Associativity", contravariantAssoc @tC genF genT obs),
      ("Naturality", contravariantNaturality @tC genF genT obs)
    ]

contravariantAssoc ::
  forall tC f r.
  ( Semigroupal (->) tC (,) f,
    Contravariant f,
    Associative (->) tC,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (tC a b)) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantAssoc genF genT obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  y <- forAllWith (const "<opaque>") genF
  z <- forAllWith (const "<opaque>") genF
  t <- forAll (genT genInt (genT genInt genInt))
  obs (contramap (fwd (assoc @(->) @tC)) (combine @(->) @tC @(,) (combine @(->) @tC @(,) (x, y), z))) t
    === obs (combine @(->) @tC @(,) (x, combine @(->) @tC @(,) (y, z))) t

contravariantNaturality ::
  forall tC f r.
  ( Semigroupal (->) tC (,) f,
    Contravariant f,
    Associative (->) tC,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (tC a b)) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantNaturality genF genT obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  y <- forAllWith (const "<opaque>") genF
  t <- forAll (genT genInt genInt)
  let g = (+ 1) :: Int -> Int
      h = (* 2) :: Int -> Int
  obs (contramap (gbimap @(->) @(->) @(->) @tC g h) (combine @(->) @tC @(,) (x, y))) t
    === obs (combine @(->) @tC @(,) (contramap g x, contramap h y)) t

-- | Left and right unit laws for a /contravariant/ functor, observed through
-- @obs@ at a generated element. The unit laws need no tensor-shaped input.
contravariantUnitalLaws ::
  forall tC iC f r.
  ( Semigroupal (->) tC (,) f,
    Unital (->) iC () f,
    Contravariant f,
    Tensor (->) tC iC,
    Eq r,
    Show r
  ) =>
  Gen (f Int) ->
  (forall a. f a -> a -> r) ->
  Laws
contravariantUnitalLaws genF obs =
  Laws
    "Unital"
    [ ("Left Unit", contravariantUnitL @tC @iC genF obs),
      ("Right Unit", contravariantUnitR @tC @iC genF obs)
    ]

contravariantUnitL ::
  forall tC iC f r.
  ( Semigroupal (->) tC (,) f,
    Unital (->) iC () f,
    Contravariant f,
    Tensor (->) tC iC,
    Eq r,
    Show r
  ) =>
  Gen (f Int) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantUnitL genF obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  a <- forAll genInt
  obs (contramap (bwd (unitl @(->) @tC)) (combine @(->) @tC @(,) (introduce @(->) @iC @() (), x))) a
    === obs x a

contravariantUnitR ::
  forall tC iC f r.
  ( Semigroupal (->) tC (,) f,
    Unital (->) iC () f,
    Contravariant f,
    Tensor (->) tC iC,
    Eq r,
    Show r
  ) =>
  Gen (f Int) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantUnitR genF obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  a <- forAll genInt
  obs (contramap (bwd (unitr @(->) @tC)) (combine @(->) @tC @(,) (x, introduce @(->) @iC @() ()))) a
    === obs x a

-- | Every 'contravariantSemigroupalLaws' and 'contravariantUnitalLaws' property
-- together, for a full contravariant 'Monoidal' instance.
contravariantMonoidalLaws ::
  forall tC iC f r.
  ( Monoidal (->) tC iC (,) () f,
    Contravariant f,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (tC a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (tC a b)) ->
  (forall a. f a -> a -> r) ->
  Laws
contravariantMonoidalLaws genF genT obs =
  Laws
    "Monoidal"
    ( lawsProperties (contravariantSemigroupalLaws @tC genF genT obs)
        <> lawsProperties (contravariantUnitalLaws @tC @iC genF obs)
    )
