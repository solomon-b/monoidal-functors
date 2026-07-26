{-# LANGUAGE CPP #-}

module Data.Functor.Monoidal.Specialized
  ( -- * Applicative
    pure,
    liftA2,
    (<*>),
    (*>),
    (<*),

    -- * Alternative
    empty,
    (<|>),
    liftAlt2,

    -- * Semialign
    align,
    alignWith,

    -- * Divisible
    divide,
    conquer,
    divided,
    conquered,
    liftD,

    -- * Decidable
    lose,
    choose,
    chosen,
    lost,

    -- * Selection
    decide,
    branch,
    select,
  )
where

--------------------------------------------------------------------------------

import Data.Bifunctor.Monoidal.Specialized (merge')
import Data.Functor.Contravariant (Contravariant (..), Op (..))
import Data.Functor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import Data.These (These)
import Data.Void (Void, absurd)
#if MIN_VERSION_base(4,18,0)
import Prelude hiding ((<*>), (*>), (<*), liftA2, pure)
#else
import Prelude hiding ((<*>), (*>), (<*), pure)
#endif

--------------------------------------------------------------------------------

-- $setup
-- >>> :set -dppr-cols=1000
-- >>> import Prelude hiding (pure, (<*>), (*>), (<*))
-- >>> import Data.Functor.Contravariant (Predicate (..), getPredicate)
-- >>> import Data.Functor.Identity (Identity (..))
-- >>> import Data.These (These (..), these)
-- >>> import Data.Void (Void)

--------------------------------------------------------------------------------

-- | 'Control.Applicative.pure' specialized to a 'Unital' functor.
--
-- ==== __Examples__
--
-- >>> pure @Maybe (5 :: Int)
-- Just 5
pure :: (Functor f, Unital (->) () () f) => a -> f a
pure a = a <$ introduce @_ @() @() ()

-- | 'Control.Applicative.liftA2' specialized to a 'Semigroupal' functor.
liftA2 :: (Functor f, Semigroupal (->) (,) (,) f) => (a -> b -> c) -> f a -> f b -> f c
liftA2 f fa fb = uncurry f <$> combine (fa, fb)

infixl 4 <*>

-- | 'Control.Applicative.<*>' specialized to a 'Semigroupal' functor.
--
-- ==== __Examples__
--
-- >>> Just not <*> Just True
-- Just False
(<*>) :: (Functor f, Semigroupal (->) (,) (,) f) => f (a -> b) -> f a -> f b
ff <*> fa = liftA2 ($) ff fa

infixl 4 *>

-- | Sequence two actions, keeping the result of the second.
--
-- ==== __Examples__
--
-- >>> Just (1 :: Int) *> Just 2
-- Just 2
(*>) :: (Functor f, Semigroupal (->) (,) (,) f) => f a -> f b -> f b
(*>) = liftA2 (const id)

infixl 4 <*

-- | Sequence two actions, keeping the result of the first.
--
-- ==== __Examples__
--
-- >>> Just (1 :: Int) <* Just 2
-- Just 1
(<*) :: (Functor f, Semigroupal (->) (,) (,) f) => f a -> f b -> f a
(<*) = liftA2 const

--------------------------------------------------------------------------------

infixl 3 <|>

-- | 'Control.Applicative.<|>' specialized to a 'Semigroupal' functor over 'Either'.
--
-- ==== __Examples__
--
-- >>> Just (1 :: Int) <|> Just 2
-- Just 1
--
-- >>> (Nothing :: Maybe Int) <|> Just 2
-- Just 2
(<|>) :: (Functor f, Semigroupal (->) Either (,) f) => f a -> f a -> f a
fa <|> fb = liftAlt2 merge' fa fb

-- | 'Control.Applicative.empty' specialized to a 'Unital' functor over 'Void'.
--
-- ==== __Examples__
--
-- >>> empty :: Maybe Int
-- Nothing
empty :: forall f a. (Functor f, Unital (->) Void () f) => f a
empty = absurd <$> introduce @(->) @Void @() @f ()

-- | Combine two actions under a function of their sum.
--
-- ==== __Examples__
--
-- >>> liftAlt2 (either negate id) (Just (3 :: Int)) (Nothing :: Maybe Int)
-- Just (-3)
liftAlt2 :: (Functor f, Semigroupal (->) Either (,) f) => (Either a b -> c) -> f a -> f b -> f c
liftAlt2 f fa fb = f <$> combine (fa, fb)

--------------------------------------------------------------------------------

-- | 'Data.Align.align' specialized to a 'Semigroupal' functor over 'These'.
--
-- ==== __Examples__
--
-- >>> align (Just (1 :: Int)) (Just (2 :: Int))
-- Just (These 1 2)
--
-- >>> align (Just (1 :: Int)) (Nothing :: Maybe Int)
-- Just (This 1)
align :: (Functor f, Semigroupal (->) These (,) f) => f a -> f b -> f (These a b)
align = curry combine

-- | 'Data.Align.alignWith' specialized to a 'Semigroupal' functor over 'These'.
--
-- ==== __Examples__
--
-- >>> alignWith (these id id (+)) [1, 2 :: Int] [10, 20, 30]
-- [11,22,30]
alignWith :: (Functor f, Semigroupal (->) These (,) f) => (These a b -> c) -> f a -> f b -> f c
alignWith f fa fb = f <$> combine @_ @These (fa, fb)

--------------------------------------------------------------------------------

-- | 'Data.Functor.Contravariant.Divisible.divide' specialized to a 'Semigroupal' functor.
--
-- ==== __Examples__
--
-- >>> getPredicate (divide (\x -> (x, x)) (Predicate even) (Predicate (> 0))) (4 :: Int)
-- True
divide :: (Contravariant f, Semigroupal (->) (,) (,) f) => (c -> (a, b)) -> f a -> f b -> f c
divide f fa fb = contramap f $ combine (fa, fb)

-- | 'Data.Functor.Contravariant.Divisible.conquer' specialized to a 'Unital' functor.
--
-- ==== __Examples__
--
-- >>> getPredicate (conquer :: Predicate Int) 5
-- True
conquer :: (Contravariant f, Unital (->) () () f) => f a
conquer = contramap (const ()) conquered

-- | Combine two contravariant actions into one over their product.
--
-- ==== __Examples__
--
-- >>> getPredicate (divided (Predicate even) (Predicate (> 0))) (4 :: Int, 1 :: Int)
-- True
divided :: (Semigroupal (->) (,) (,) f) => f a -> f b -> f (a, b)
divided = curry combine

-- | The unit of 'divided'.
--
-- ==== __Examples__
--
-- >>> getPredicate conquered ()
-- True
conquered :: (Unital (->) () () f) => f ()
conquered = introduce ()

-- | Contravariantly map over a 'Monoidal' functor.
--
-- ==== __Examples__
--
-- >>> getPredicate (liftD (+ 1) (Predicate even)) (3 :: Int)
-- True
liftD :: (Contravariant f, Monoidal (->) (,) () (,) () f) => (a -> b) -> f b -> f a
liftD f = divide ((,) () . f) conquer

--------------------------------------------------------------------------------

-- | 'Data.Functor.Contravariant.Decidable.lose' specialized to a 'Unital' functor over 'Void'.
lose :: (Contravariant f, Unital (->) Void () f) => (a -> Void) -> f a
lose f = contramap f lost

-- | 'Data.Functor.Contravariant.Decidable.choose' specialized to a 'Semigroupal' functor over 'Either'.
--
-- ==== __Examples__
--
-- >>> getPredicate (choose (\n -> if even n then Left n else Right n) (Predicate (> 0)) (Predicate (< 0))) (4 :: Int)
-- True
choose :: (Contravariant f, Semigroupal (->) Either (,) f) => (c -> Either a b) -> f a -> f b -> f c
choose f fa fb = contramap f $ combine (fa, fb)

-- | Combine two contravariant actions into one over their sum.
--
-- ==== __Examples__
--
-- >>> getPredicate (chosen (Predicate even) (Predicate (> 0))) (Left 4 :: Either Int Int)
-- True
chosen :: (Contravariant f, Semigroupal (->) Either (,) f) => f b -> f c -> f (Either b c)
chosen = curry combine

-- | The unit of 'chosen'.
--
-- ==== __Examples__
--
-- >>> lost :: Maybe Void
-- Nothing
lost :: (Unital (->) Void () f) => f Void
lost = introduce ()

--------------------------------------------------------------------------------

-- | Pull a choice out of a functor.
--
-- ==== __Examples__
--
-- >>> decide (Identity (Left 5) :: Identity (Either Int Int))
-- Left (Identity 5)
decide :: (Functor f, Semigroupal Op Either Either f) => f (Either a b) -> Either (f a) (f b)
decide = getOp combine

-- | Branch on a choice, applying the matching function.
--
-- ==== __Examples__
--
-- >>> branch (Identity (Left 5) :: Identity (Either Int Int)) (Identity negate) (Identity id)
-- Identity (-5)
branch :: (Functor f, Semigroupal Op Either Either f, Semigroupal (->) (,) (,) f) => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch fab fac fbc =
  case decide fab of
    Left fa -> (\(a, f) -> f a) <$> combine (fa, fac)
    Right fb -> (\(b, f) -> f b) <$> combine (fb, fbc)

-- | Apply the function only when the value is a 'Left'.
--
-- ==== __Examples__
--
-- >>> select (Identity (Left 5) :: Identity (Either Int Int)) (Identity negate)
-- Identity (-5)
select :: (Functor f, Semigroupal Op Either Either f, Monoidal (->) (,) () (,) () f) => f (Either a b) -> f (a -> b) -> f b
select fa ff = branch fa ff (id <$ introduce @(->) @() ())
