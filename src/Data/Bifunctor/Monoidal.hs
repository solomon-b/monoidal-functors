module Data.Bifunctor.Monoidal
  ( -- * Semigroupal
    Semigroupal (..),

    -- * Unital
    Unital (..),

    -- * Monoidal
    Monoidal,
  )
where

--------------------------------------------------------------------------------

import Control.Applicative (Alternative (..), Applicative (..), pure, (<$>))
import Control.Arrow (Kleisli (..))
import Control.Category (Category (..))
import Control.Category.Cartesian (Cocartesian (..), Semicartesian (..))
import Control.Category.Tensor (Associative, Iso (..), Tensor (..))
import Control.Monad (Functor (..), Monad)
import Data.Biapplicative (Biapplicative (..), Bifunctor (..))
import Data.Bifunctor.Clown (Clown)
import Data.Bifunctor.Joker (Joker (..))
import Data.Either (Either, either)
import Data.Function (const, ($))
import Data.Profunctor (Forget (..), Profunctor (..), Star (..), Strong (..))
import Data.Semigroupoid (Semigroupoid (..))
import Data.These (These (..), these)
import Data.Tuple (fst, snd, uncurry)
import Data.Void (Void, absurd)
import Prelude (Either (..))

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A bifunctor \(F : \mathcal{C_1} \times \mathcal{C_2} \to \mathcal{D}\) is 'Semigroupal' if it supports a
-- natural transformation \(\phi_{AB,CD} : F\ A\ B \bullet F\ C\ D \to F\ (A \otimes C)\ (B \otimes D)\), which we call 'combine'.
--
-- === Laws
--
-- __Associativity:__
--
-- \[
-- \require{AMScd}
-- \begin{CD}
-- (F A B \bullet F C D) \bullet F X Y                      @>>{\alpha_{\mathcal{D}}}>                              F A B \bullet (F C D \bullet F X Y) \\
-- @VV{\phi_{AB,CD} \bullet 1}V                                                                                     @VV{1 \bullet \phi_{CD,FY}}V \\
-- F (A \otimes C) (B \otimes D) \bullet F X Y              @.                                                      F A B \bullet (F (C \otimes X) (D \otimes Y) \\
-- @VV{\phi_{(A \otimes C)(B \otimes D),XY}}V                                                                       @VV{\phi_{AB,(C \otimes X)(D \otimes Y)}}V \\
-- F ((A \otimes C) \otimes X)  ((B \otimes D) \otimes Y)   @>>{F \alpha_{\mathcal{C_1}}} \alpha_{\mathcal{C_2}}>   F (A \otimes (C \otimes X)) (B \otimes (D \otimes Y)) \\
-- \end{CD}
-- \]
--
-- @
-- 'combine' 'Control.Category..' 'Control.Category.Tensor.grmap' 'combine' 'Control.Category..' 'bwd' 'Control.Category.Tensor.assoc' ≡ 'fmap' ('bwd' 'Control.Category.Tensor.assoc') 'Control.Category..' 'combine' 'Control.Category..' 'Control.Category.Tensor.glmap' 'combine'
-- @
class (Associative cat t1, Associative cat t2, Associative cat to) => Semigroupal cat t1 t2 to f where
  -- | A natural transformation \(\phi_{AB,CD} : F\ A\ B \bullet F\ C\ D \to F\ (A \otimes C)\ (B \otimes D)\).
  --
  -- ==== __Examples__
  --
  -- >>> :t combine @(->) @(,) @(,) @(,) @(,)
  -- combine @(->) @(,) @(,) @(,) @(,) :: ((x, y), (x', y')) -> ((x, x'), (y, y'))
  --
  -- >>> combine @(->) @(,) @(,) @(,) @(,) ((True, "Hello"), ((), "World"))
  -- ((True,()),("Hello","World"))
  --
  -- >>> combine @(->) @(,) @(,) @(,) @(->) (show, (>10)) (True, 11)
  -- ("True",True)
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
  combine = uncurry bimap

instance Semigroupal (->) Either Either (,) (->) where
  combine :: (x -> y, x' -> y') -> Either x x' -> Either y y'
  combine fs = either (Left . fst fs) (Right . snd fs)

instance Applicative f => Semigroupal (->) (,) (,) (,) (Joker f) where
  combine :: (Joker f x y, Joker f x' y') -> Joker f (x, x') (y, y')
  combine = uncurry $ biliftA2 (,) (,)

instance Alternative f => Semigroupal (->) Either Either (,) (Joker f) where
  combine :: (Joker f x y, Joker f x' y') -> Joker f (Either x x') (Either y y')
  combine = uncurry $ biliftA2 (\_ x' -> Right x') (\_ y' -> Right y')

instance Functor f => Semigroupal (->) Either Either Either (Joker f) where
  combine :: Either (Joker f x y) (Joker f x' y') -> Joker f (Either x x') (Either y y')
  combine = either (Joker . fmap Left . runJoker) (Joker . fmap Right . runJoker)

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

instance Applicative f => Semigroupal (->) These These (,) (Star f) where
  combine :: (Star f x y, Star f x' y') -> Star f (These x x') (These y y')
  combine (Star fxy, Star fxy') = Star $ these (fmap This . fxy) (fmap That . fxy') (\x x' -> liftA2 These (fxy x) (fxy' x'))

instance Alternative f => Semigroupal (->) These These These (Star f) where
  combine :: Applicative f => These (Star f x y) (Star f x' y') -> Star f (These x x') (These y y')
  combine = \case
    This (Star fxy) -> Star $ these (fmap This . fxy) (const empty) (\x _ -> This <$> fxy x)
    That (Star fxy') -> Star $ these (const empty) (fmap That . fxy') (\_ x' -> That <$> fxy' x')
    These (Star fxy) (Star fxy') -> Star $ these (fmap This . fxy) (fmap That . fxy') (\x x' -> liftA2 These (fxy x) (fxy' x'))

instance Alternative f => Semigroupal (->) Either Either Either (Star f) where
  combine :: Either (Star f x y) (Star f x' y') -> Star f (Either x x') (Either y y')
  combine = \case
    Left (Star fxy) -> Star $ either (fmap Left . fxy) (const empty)
    Right (Star fxy') -> Star $ either (const empty) (fmap Right . fxy')

instance Alternative f => Semigroupal (->) (,) Either (,) (Star f) where
  combine :: (Star f x y, Star f x' y') -> Star f (x, x') (Either y y')
  combine (Star f, Star g) = Star $ \(x, x') -> (Left <$> f x) <|> (Right <$> g x')

instance Applicative f => Semigroupal (->) (,) (,) (,) (Kleisli f) where
  combine :: (Kleisli f x y, Kleisli f x' y') -> Kleisli f (x, x') (y, y')
  combine (Kleisli fxy, Kleisli fxy') = Kleisli $ \(x, x') -> liftA2 (,) (fxy x) (fxy' x')

instance Functor f => Semigroupal (->) Either Either (,) (Kleisli f) where
  combine :: (Kleisli f x y, Kleisli f x' y') -> Kleisli f (Either x x') (Either y y')
  combine (Kleisli fxy, Kleisli fxy') = Kleisli $ either (fmap Left . fxy) (fmap Right . fxy')

instance Applicative f => Semigroupal (->) These These (,) (Kleisli f) where
  combine :: (Kleisli f x y, Kleisli f x' y') -> Kleisli f (These x x') (These y y')
  combine (Kleisli fxy, Kleisli fxy') = Kleisli $ these (fmap This . fxy) (fmap That . fxy') (\x x' -> liftA2 These (fxy x) (fxy' x'))

instance Alternative f => Semigroupal (->) These These These (Kleisli f) where
  combine :: Applicative f => These (Kleisli f x y) (Kleisli f x' y') -> Kleisli f (These x x') (These y y')
  combine = \case
    This (Kleisli fxy) -> Kleisli $ these (fmap This . fxy) (const empty) (\x _ -> This <$> fxy x)
    That (Kleisli fxy') -> Kleisli $ these (const empty) (fmap That . fxy') (\_ x' -> That <$> fxy' x')
    These (Kleisli fxy) (Kleisli fxy') -> Kleisli $ these (fmap This . fxy) (fmap That . fxy') (\x x' -> liftA2 These (fxy x) (fxy' x'))

instance Alternative f => Semigroupal (->) Either Either Either (Kleisli f) where
  combine :: Either (Kleisli f x y) (Kleisli f x' y') -> Kleisli f (Either x x') (Either y y')
  combine = \case
    Left (Kleisli fxy) -> Kleisli $ either (fmap Left . fxy) (const empty)
    Right (Kleisli fxy') -> Kleisli $ either (const empty) (fmap Right . fxy')

instance Alternative f => Semigroupal (->) (,) Either (,) (Kleisli f) where
  combine :: (Kleisli f x y, Kleisli f x' y') -> Kleisli f (x, x') (Either y y')
  combine (Kleisli f, Kleisli g) = Kleisli $ \(x, x') -> (Left <$> f x) <|> (Right <$> g x')

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

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A bifunctor \(F : \mathcal{C_1} \times \mathcal{C_2} \to \mathcal{D}\) is 'Unital' if it supports a morphism
-- \(\phi : I_{\mathcal{D}} \to F\ I_{\mathcal{C_1}}\ I_{\mathcal{C_2}}\), which we call 'introduce'.
class Unital cat i1 i2 io f where
  -- | @introduce@ maps from the identity in \(\mathcal{C_1} \times \mathcal{C_2}\) to the
  -- identity in \(\mathcal{D}\).
  --
  -- ==== __Examples__
  --
  -- >>> introduce @(->) @() @() @() @(,) ()
  -- ((),())
  --
  -- >>> :t introduce @(->) @Void @() @() @Either
  -- introduce @(->) @Void @() @() @Either :: () -> Either Void ()
  --
  -- >>> introduce @(->) @Void @() @() @Either ()
  -- Right ()
  introduce :: cat io (f i1 i2)

instance (Profunctor p, Category p) => Unital (->) () () () (StrongCategory p) where
  introduce :: () -> StrongCategory p () ()
  introduce () = StrongCategory id

instance Unital (->) () () () (,) where
  introduce :: () -> ((), ())
  introduce = split

instance Unital (->) Void Void Void (,) where
  introduce :: Void -> (Void, Void)
  introduce = spawn

instance Unital (->) Void Void Void Either where
  introduce :: Void -> Either Void Void
  introduce = bwd unitr

instance Unital (->) Void () () Either where
  introduce :: () -> Either Void ()
  introduce = Right

instance Unital (->) () () () (->) where
  introduce :: () -> () -> ()
  introduce () () = ()

instance Unital (->) Void Void Void (->) where
  introduce :: Void -> Void -> Void
  introduce = absurd

instance (Unital (->) Void Void () (->)) where
  introduce :: () -> Void -> Void
  introduce () = absurd

instance Applicative f => Unital (->) () () () (Joker f) where
  introduce :: () -> Joker f () ()
  introduce = Joker . pure

instance Alternative f => Unital (->) Void Void () (Joker f) where
  introduce :: () -> Joker f Void Void
  introduce () = Joker empty

instance Unital (->) Void Void Void (Joker f) where
  introduce :: Void -> Joker f Void Void
  introduce = absurd

instance Applicative f => Unital (->) () () () (Star f) where
  introduce :: () -> Star f () ()
  introduce () = Star pure

instance Unital (->) Void Void () (Star f) where
  introduce :: () -> Star f Void Void
  introduce () = Star absurd

instance Alternative f => Unital (->) Void Void Void (Star f) where
  introduce :: Void -> Star f Void Void
  introduce = absurd

instance Alternative f => Unital (->) () Void () (Star f) where
  introduce :: () -> Star f () Void
  introduce () = Star $ const empty

instance Applicative f => Unital (->) () () () (Kleisli f) where
  introduce :: () -> Kleisli f () ()
  introduce () = Kleisli pure

instance Unital (->) Void Void () (Kleisli f) where
  introduce :: () -> Kleisli f Void Void
  introduce () = Kleisli absurd

instance Alternative f => Unital (->) Void Void Void (Kleisli f) where
  introduce :: Void -> Kleisli f Void Void
  introduce = absurd

instance Alternative f => Unital (->) () Void () (Kleisli f) where
  introduce :: () -> Kleisli f () Void
  introduce () = Kleisli $ const empty

--------------------------------------------------------------------------------
-- Monoidal

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A bifunctor \(F : \mathcal{C_1} \times \mathcal{C_2} \to \mathcal{D}\) is 'Monoidal' if it maps between \(\mathcal{C_1} \times \mathcal{C_2}\)
-- and \(\mathcal{D}\) while preserving their monoidal structure. Eg., a homomorphism of monoidal categories.
--
-- See <https://ncatlab.org/nlab/show/monoidal+functor NCatlab> for more details.
--
-- === Laws
--
-- __Right Unitality:__
--
-- \[
-- \require{AMScd}
-- \begin{CD}
-- F A B \bullet I_{\mathcal{D}}   @>{1 \bullet \phi}>>                                     F A B \bullet F I_{\mathcal{C_{1}}} I_{\mathcal{C_{2}}}\\
-- @VV{\rho_{\mathcal{D}}}V                                                                 @VV{\phi AB,I_{\mathcal{C_{1}}}I_{\mathcal{C_{2}}}}V \\
-- F A B                           @<<{F \rho_{\mathcal{C_{1}}} \rho_{\mathcal{C_{2}}}}<    F (A \otimes I_{\mathcal{C_{1}}}) (B \otimes I_{\mathcal{C_{2}}})
-- \end{CD}
-- \]
--
-- @
-- 'combine' 'Control.Category..' 'Control.Category.Tensor.grmap' 'introduce' ≡ 'bwd' 'unitr' 'Control.Category..' 'fwd' 'unitr'
-- @
--
-- __ Left Unitality__:
--
-- \[
-- \begin{CD}
-- I_{\mathcal{D}} \bullet F A B   @>{\phi \bullet 1}>>                                          F I_{\mathcal{C_{1}}} I_{\mathcal{C_{2}}} \bullet F A B\\
-- @VV{\lambda_{\mathcal{D}}}V                                                                   @VV{I_{\mathcal{C_{1}}}I_{\mathcal{C_{2}}},\phi AB}V \\
-- F A B                           @<<{F \lambda_{\mathcal{C_{1}}} \lambda_{\mathcal{C_{2}}}}<   F (I_{\mathcal{C_{1}}} \otimes A) (I_{\mathcal{C_{2}}} \otimes B)
-- \end{CD}
-- \]
--
-- @
-- 'combine' 'Control.Category..' 'Control.Category.Tensor.glmap' 'introduce' ≡ 'fmap' ('bwd' 'unitl') 'Control.Category..' 'fwd' 'unitl'
-- @
class
  ( Tensor cat t1 i1,
    Tensor cat t2 i2,
    Tensor cat to io,
    Semigroupal cat t1 t2 to f,
    Unital cat i1 i2 io f
  ) =>
  Monoidal cat t1 i1 t2 i2 to io f

instance (Strong p, Semigroupoid p, Category p) => Monoidal (->) (,) () (,) () (,) () (StrongCategory p)

instance Monoidal (->) (,) () (,) () (,) () (,)

instance Monoidal (->) Either Void Either Void Either Void (,)

instance Monoidal (->) Either Void Either Void Either Void Either

instance Monoidal (->) Either Void (,) () (,) () Either

instance Monoidal (->) These Void (,) () (,) () Either

instance Monoidal (->) (,) () (,) () (,) () (->)

instance Monoidal (->) Either Void Either Void (,) () (->)

instance Applicative f => Monoidal (->) (,) () (,) () (,) () (Joker f)

instance Alternative f => Monoidal (->) Either Void Either Void (,) () (Joker f)

instance Functor f => Monoidal (->) Either Void Either Void Either Void (Joker f)

instance Applicative f => Monoidal (->) (,) () (,) () (,) () (Star f)

instance Functor f => Monoidal (->) Either Void Either Void (,) () (Star f)

instance Applicative f => Monoidal (->) These Void These Void (,) () (Star f)

instance Alternative f => Monoidal (->) Either Void Either Void Either Void (Star f)

instance Alternative f => Monoidal (->) These Void These Void These Void (Star f)

instance Alternative f => Monoidal (->) (,) () Either Void (,) () (Star f)

instance Applicative f => Monoidal (->) (,) () (,) () (,) () (Kleisli f)

instance Functor f => Monoidal (->) Either Void Either Void (,) () (Kleisli f)

instance Applicative f => Monoidal (->) These Void These Void (,) () (Kleisli f)

instance Alternative f => Monoidal (->) Either Void Either Void Either Void (Kleisli f)

instance Alternative f => Monoidal (->) These Void These Void These Void (Kleisli f)

instance Alternative f => Monoidal (->) (,) () Either Void (,) () (Kleisli f)

newtype StrongCategory p a b = StrongCategory (p a b)
  deriving (Functor, Applicative, Monad, Profunctor, Category)

instance Semigroupoid p => Semigroupoid (StrongCategory p) where
  o :: StrongCategory p b c -> StrongCategory p a b -> StrongCategory p a c
  o (StrongCategory f) (StrongCategory g) = StrongCategory (f `o` g)

instance (Strong p, Semigroupoid p) => Semigroupal (->) (,) (,) (,) (StrongCategory p) where
  combine :: (StrongCategory p x y, StrongCategory p x' y') -> StrongCategory p (x, x') (y, y')
  combine (StrongCategory pxy, StrongCategory pxy') = StrongCategory $ first' pxy `o` second' pxy'
