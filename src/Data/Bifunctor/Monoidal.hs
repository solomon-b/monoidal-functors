module Data.Bifunctor.Monoidal where

import Prelude hiding ((.), id)
import Control.Applicative
import Control.Category
import Control.Category.Tensor
import Data.Biapplicative
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Profunctor
import Data.These

class (Associative t1 cat, Associative t2 cat, Associative to cat) => Semigroupal cat t1 t2 to f where
  combine :: cat (to (f x y) (f x' y')) (f (t1 x x') (t2 y y'))

instance Profunctor p => Semigroupal (->) (,) Either Either p where
  combine :: Either (p x y) (p x' y') -> p (x, x') (Either y y')
  combine = either (dimap fst Left) (dimap snd Right)

instance Semigroupal (->) (,) (,) (,) (,) where
  combine :: ((x, y), (x', y')) -> ((x, x'), (y, y'))
  combine ((x, y), (x', y')) = ((x, x'), (y, y'))
  -- NOTE: This version could be used for a more general abstraction
  -- of products in a category:
  -- combine =
  --   let fwd' = fwd assoc
  --       bwd' = bwd assoc
  --   in second swap . swap . fwd' . swap . first (bwd' . first swap) . fwd'

instance Semigroupal (->) Either Either Either (,) where
  combine :: Either (x, y) (x', y') -> (Either x x', Either y y')
  combine = either (bimap Left Left) (bimap Right Right)

instance Semigroupal (->) Either Either Either Either where
  combine :: Either (Either x y) (Either x' y') -> Either (Either x x') (Either y y')
  combine = either (bimap Left Left) (bimap Right Right)

instance Semigroupal (->) Either (,) (,) Either where
  combine :: (Either x y, Either x' y') -> Either (Either x x') (y, y')
  combine = \case
    (Left x, Left _) -> Left $ Left x
    (Left x, Right _) -> Left $ Left x
    (Right _, Left x') -> Left $ Right x'
    (Right y, Right y') -> Right (y, y')

instance Semigroupal (->) These (,) (,) Either where
  combine :: (Either x y, Either x' y') -> Either (These x x') (y, y')
  combine = \case
    (Left x, Left x') -> Left $ These x x'
    (Left x, Right _) -> Left $ This x
    (Right _, Left x') -> Left $ That x'
    (Right y, Right y') -> Right (y, y')

instance Semigroupal (->) (,) (,) (,) (->) where
  combine :: (x -> y, x' -> y') -> (x, x') -> (y, y')
  combine fs = uncurry bimap fs

instance Semigroupal (->) Either Either (,) (->) where
  combine :: (x -> y, x' -> y') -> Either x x' -> Either y y'
  combine fs = either (Left . fst fs) (Right . snd fs)

instance Applicative f => Semigroupal (->) (,) (,) (,) (Joker f) where
  combine :: (Joker f x y, Joker f x' y') -> Joker f (x, x') (y, y')
  combine = uncurry $ biliftA2 (,) (,)

instance Alternative f => Semigroupal (->) Either Either (,) (Joker f) where
  combine :: (Joker f x y, Joker f x' y') -> Joker f (Either x x') (Either y y')
  combine  = uncurry $ biliftA2 (\_ x' -> Right x') (\_ y' -> Right y')

instance Applicative f => Semigroupal (->) (,) (,) (,) (Clown f) where
  combine :: (Clown f x y, Clown f x' y') -> Clown f (x, x') (y, y')
  combine = uncurry $ biliftA2 (,) (,)

instance Alternative f => Semigroupal (->) Either Either (,) (Clown f) where
  combine :: (Clown f x y, Clown f x' y') -> Clown f (Either x x') (Either y y')
  combine = uncurry $ biliftA2 (\_ x' -> Right x') (\_ y' -> Right y')

instance Applicative f => Semigroupal (->) (,) (,) (,) (Star f) where
  combine :: (Star f x y, Star f x' y') -> Star f (x, x') (y, y')
  combine (Star fxy, Star fxy') = Star $ \(x, x') -> liftA2 (,) (fxy x) (fxy' x')

instance Functor f => Semigroupal (->) Either Either (,) (Star f) where
  combine :: (Star f x y, Star f x' y') -> Star f (Either x x') (Either y y')
  combine (Star fxy, Star fxy') = Star $ either (fmap Left . fxy) (fmap Right . fxy')

instance Alternative f => Semigroupal (->) Either Either Either (Star f) where
  combine :: Either (Star f x y) (Star f x' y') -> Star f (Either x x') (Either y y')
  combine = \case
    Left (Star fxy) -> Star $ either (fmap Left . fxy) (const empty)
    Right (Star fxy') -> Star $ either (const empty) (fmap Right . fxy')

instance Alternative f => Semigroupal (->) (,) Either (,) (Star f) where
  combine :: (Star f x y, Star f x' y') -> Star f (x, x') (Either y y')
  combine (Star f, Star g) = Star $ \(x, x') -> (Left <$> f x) <|> (Right <$> g x')

instance Alternative f => Semigroupal (->) (,) (,) (,) (Forget (f r)) where
  combine :: (Forget (f r) x y, Forget (f r) x' y') -> Forget (f r) (x, x') (y, y')
  combine (Forget f, Forget g) = Forget $ \(x, x') -> f x <|> g x'

instance Semigroupal (->) Either Either (,) (Forget (f r)) where
  combine :: (Forget (f r) x y, Forget (f r) x' y') -> Forget (f r) (Either x x') (Either y y')
  combine (Forget f, Forget g) = Forget $ either f g

instance Alternative f => Semigroupal (->) Either Either Either (Forget (f r)) where
  combine :: Either (Forget (f r) x y) (Forget (f r) x' y') -> Forget (f r) (Either x x') (Either y y')
  combine = \case
    Left (Forget f) -> Forget $ either f (const empty)
    Right (Forget g) -> Forget $ either (const empty) g

instance Alternative f => Semigroupal (->) (,) Either (,) (Forget (f r)) where
  combine :: (Forget (f r) x y, Forget (f r) x' y') -> Forget (f r) (x, x') (Either y y')
  combine (Forget f, Forget g) = Forget $ \(x, x') -> f x <|> g x'
