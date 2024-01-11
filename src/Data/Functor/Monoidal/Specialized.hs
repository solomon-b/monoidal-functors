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

pure :: (Functor f, Unital (->) () () f) => a -> f a
pure a = a <$ introduce @_ @() @() ()

liftA2 :: (Functor f, Semigroupal (->) (,) (,) f) => (a -> b -> c) -> f a -> f b -> f c
liftA2 f fa fb = uncurry f <$> combine (fa, fb)

infixl 4 <*>

(<*>) :: (Functor f, Semigroupal (->) (,) (,) f) => f (a -> b) -> f a -> f b
ff <*> fa = liftA2 ($) ff fa

infixl 4 *>

(*>) :: (Functor f, Semigroupal (->) (,) (,) f) => f a -> f b -> f b
(*>) = liftA2 (const id)

infixl 4 <*

(<*) :: (Functor f, Semigroupal (->) (,) (,) f) => f a -> f b -> f a
(<*) = liftA2 const

--------------------------------------------------------------------------------

infixl 3 <|>

(<|>) :: (Functor f, Semigroupal (->) Either (,) f) => f a -> f a -> f a
fa <|> fb = liftAlt2 merge' fa fb

empty :: forall f a. (Functor f, Unital (->) Void () f) => f a
empty = absurd <$> introduce @(->) @Void @() @f ()

liftAlt2 :: (Functor f, Semigroupal (->) Either (,) f) => (Either a b -> c) -> f a -> f b -> f c
liftAlt2 f fa fb = f <$> combine (fa, fb)

--------------------------------------------------------------------------------

align :: (Functor f, Semigroupal (->) These (,) f) => f a -> f b -> f (These a b)
align = curry combine

alignWith :: (Functor f, Semigroupal (->) These (,) f) => (These a b -> c) -> f a -> f b -> f c
alignWith f fa fb = f <$> combine @_ @These (fa, fb)

--------------------------------------------------------------------------------

divide :: (Contravariant f, Semigroupal (->) (,) (,) f) => (c -> (a, b)) -> f a -> f b -> f c
divide f fa fb = contramap f $ combine (fa, fb)

conquer :: (Contravariant f, Unital (->) () () f) => f a
conquer = contramap (const ()) conquered

divided :: (Semigroupal (->) (,) (,) f) => f a -> f b -> f (a, b)
divided = curry combine

conquered :: (Unital (->) () () f) => f ()
conquered = introduce ()

liftD :: (Contravariant f, Monoidal (->) (,) () (,) () f) => (a -> b) -> f b -> f a
liftD f = divide ((,) () . f) conquer

--------------------------------------------------------------------------------

lose :: (Contravariant f, Unital (->) Void () f) => (a -> Void) -> f a
lose f = contramap f lost

choose :: (Contravariant f, Semigroupal (->) Either (,) f) => (c -> Either a b) -> f a -> f b -> f c
choose f fa fb = contramap f $ combine (fa, fb)

chosen :: (Contravariant f, Semigroupal (->) Either (,) f) => f b -> f c -> f (Either b c)
chosen = curry combine

lost :: (Unital (->) Void () f) => f Void
lost = introduce ()

--------------------------------------------------------------------------------

decide :: (Functor f, Semigroupal Op Either Either f) => f (Either a b) -> Either (f a) (f b)
decide = getOp combine

branch :: (Functor f, Semigroupal Op Either Either f, Semigroupal (->) (,) (,) f) => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch fab fac fbc =
  case decide fab of
    Left fa -> (\(a, f) -> f a) <$> combine (fa, fac)
    Right fb -> (\(b, f) -> f b) <$> combine (fb, fbc)

select :: (Functor f, Semigroupal Op Either Either f, Monoidal (->) (,) () (,) () f) => f (Either a b) -> f (a -> b) -> f b
select fa ff = branch fa ff (id <$ introduce @(->) @() ())
