module Data.Functor.Monoidal
  ( -- * Semigroupal
    Semigroupal (..),

    -- * Unital
    Unital (..),

    -- * Monoidal
    Monoidal,
  )
where

import Control.Applicative
import Control.Category.Tensor
import Data.Align
import Data.These
import Data.Void
import Prelude

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A functor \(F : \mathcal{C} \to \mathcal{D}\) is 'Semigroupal' if it supports a natural transformation
-- \(\phi_{A,B} : F\ A \bullet F\ B \to F\ (A \otimes B)\), which we call 'combine'.
--
-- === Laws
--
-- __Associativity:__
--
-- \[ 
-- \require{AMScd}
-- \begin{CD}
-- (F A \bullet F B) \bullet F C @>>{\alpha_{\mathcal{D}}}>     F A \bullet (F B \bullet F C) \\
-- @VV{\phi_{A,B} \bullet 1}V                                   @VV{1 \bullet \phi_{B,C}}V \\
-- F (A \otimes B) \bullet F C   @.                             F A \bullet (F (B \otimes C)) \\
-- @VV{\phi_{A \otimes B,C}}V                                   @VV{\phi_{A,B \otimes C}}V \\
-- F ((A \otimes B) \otimes C)   @>>{F \alpha_{\mathcal{C}}}>   F (A \otimes (B \otimes C)) \\
-- \end{CD}
-- \]
--
-- @
-- 'combine' 'Control.Category..' 'grmap' 'combine' 'Control.Category..' 'bwd' 'assoc' ≡ 'fmap' ('bwd' 'assoc') 'Control.Category..' 'combine' 'Control.Category..' 'glmap' 'combine'
-- @
class (Associative cat t1, Associative cat t0) => Semigroupal cat t1 t0 f where
  -- | @combine@ is a natural transformation from functors \(\mathcal{C} × \mathcal{C}\) to \(\mathcal{D}\).
  --
  -- ==== __Examples__
  --
  -- >>> combine @(->) @(,) @(,) @Maybe (Just True, Just "hello")
  -- Just (True,"hello")
  --
  -- >>> combine @(->) @(,) @(,) @Maybe (Just True, Nothing)
  -- Nothing
  --
  -- >>> combine @(->) @Either @(,) @Maybe (Just True, Nothing)
  -- Just (Left True)
  --
  -- >>> combine @(->) @Either @(,) @Maybe (Nothing, Just "hello")
  -- Just (Right "hello")
  combine :: (f x `t0` f x') `cat` f (x `t1` x')

instance Applicative f => Semigroupal (->) (,) (,) f where
  combine :: (f x, f x') -> f (x, x')
  combine = uncurry (liftA2 (,))

instance Alternative f => Semigroupal (->) Either (,) f where
  combine :: (f x, f x') -> f (Either x x')
  combine (fx, fx') = fmap Left fx <|> fmap Right fx'

instance Semialign f => Semigroupal (->) These (,) f where
  combine :: (f x, f x') -> f (These x x')
  combine = uncurry align

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A functor \(F : \mathcal{C} \to \mathcal{D}\) is 'Unital' if it supports a morphism \(\phi : I_{\mathcal{D}} \to F\ I_{\mathcal{C}}\),
-- which we call 'introduce'.
class Unital cat i1 i0 f where
  -- | @introduce@ maps from the identity in \(\mathcal{C}\) to the
  -- identity in \(\mathcal{D}\).
  --
  -- ==== __Examples__
  --
  -- >>> introduce @(->) @() @() @Maybe ()
  -- Just ()
  --
  -- >>> :t introduce @(->) @Void @() @Maybe 
  -- introduce @(->) @Void @() @Maybe :: () -> Maybe Void
  -- 
  -- >>> introduce @(->) @Void @() @Maybe ()
  -- Nothing
  introduce :: cat i0 (f i1)

instance Applicative f => Unital (->) () () f where
  introduce :: () -> f ()
  introduce = pure

instance Alternative f => Unital (->) Void () f where
  introduce :: () -> f Void
  introduce () = empty

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A functor \(F : \mathcal{C} \to \mathcal{D}\) is 'Monoidal' if it maps between \(\mathcal{C}\) and \(\mathcal{D}\) while
-- preserving their monoidal structure. Eg., a homomorphism of monoidal categories.
--
-- See <https://ncatlab.org/nlab/show/monoidal+functor NCatlab> for more details.
--
-- === Laws
--
-- __Right Unitality__:
--
-- \[ 
-- \require{AMScd}
-- \begin{CD}
-- F A \bullet I_{\mathcal{D}}   @>{1 \bullet \phi}>>         F A \bullet F I_{\mathcal{C}};\\
-- @VV{\rho_{\mathcal{D}}}V                                   @VV{\phi A,I_{\mathcal{C}}}V \\
-- F A                           @<<{F \rho_{\mathcal{C}}}<   F (A \otimes I_{\mathcal{C}});
-- \end{CD}
-- \]
--
-- @
--   'combine' 'Control.Category..' 'grmap' 'introduce' ≡ 'bwd' 'unitr' 'Control.Category..' 'fwd' 'unitr'
-- @
--
-- __ Left Unitality__:
--
-- \[ 
-- \begin{CD}
-- I_{\mathcal{D}} \bullet F B   @>{\phi \bullet 1}>>            F I_{\mathcal{C}} \bullet F B;\\
-- @VV{\lambda_{\mathcal{D}}}V                                   @VV{\phi I_{\mathcal{C}},B}V \\
-- F A                           @<<{F \lambda_{\mathcal{C}}}<   F (A \otimes I_{\mathcal{C}} \otimes B);
-- \end{CD}
-- \]
--
-- @
--   'combine' 'Control.Category..' 'glmap' 'introduce' ≡ 'fmap' ('bwd' 'unitl') 'Control.Category..' 'fwd' 'unitl'
-- @
class
  ( Tensor cat t1 i1
  , Tensor cat t0 i0
  , Semigroupal cat t1 t0 f
  , Unital cat i1 i0 f
  ) => Monoidal cat t1 i1 t0 i0 f

instance Applicative f => Monoidal (->) (,) () (,) () f

instance Alternative f => Monoidal (->) Either Void (,) () f

instance (Alternative f, Semialign f) => Monoidal (->) These Void (,) () f
