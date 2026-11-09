module Data.Trifunctor.Monoidal
  ( -- * Semigroupal
    Semigroupal (..),
    (|???|),
    (|***|),
    (|**+|),
    (|**&|),
    (|*+*|),
    (|*++|),
    (|*+&|),
    (|*&*|),
    (|*&+|),
    (|*&&|),
    (|+**|),
    (|+*+|),
    (|+*&|),
    (|++*|),
    (|+++|),
    (|++&|),
    (|+&*|),
    (|+&+|),
    (|+&&|),
    (|&**|),
    (|&*+|),
    (|&*&|),
    (|&+*|),
    (|&++|),
    (|&+&|),
    (|&&*|),
    (|&&+|),
    (|&&&|),

    -- * Unital
    Unital (..),

    -- * Monoidal
    Monoidal,
  )
where

--------------------------------------------------------------------------------

import Control.Category.Tensor (Associative, Tensor)
import Data.These (These)
import Prelude (Either, curry)

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A trifunctor \(F : \mathcal{C_1} \times \mathcal{C_2} \times \mathcal{C_3} \to \mathcal{D}\) is 'Semigroupal' if it supports a
-- natural transformation \(\phi_{ABC,XYZ} : F\ A\ B\ C \bullet F\ X\ Y\ Z \to F\ (A \otimes X)\ (B \otimes Y)\ (C \otimes Z)\), which we call 'combine'.
--
-- === Laws
--
-- __Associativity:__
--
-- \[
-- \require{AMScd}
-- \begin{CD}
-- (F A B C \bullet F X Y Z) \bullet F P Q R                                              @>>{\alpha_{\mathcal{D}}}>     F A B C \bullet (F X Y Z \bullet F P Q R) \\
-- @VV{\phi_{ABC,XYZ} \bullet 1}V                                                                                        @VV{1 \bullet \phi_{XYZ,PQR}}V \\
-- F (A \otimes X) (B \otimes Y) (C \otimes Z) \bullet F P Q R                            @.                             F A B C \bullet (F (X \otimes P) (Y \otimes Q) (Z \otimes R) \\
-- @VV{\phi_{(A \otimes X)(B \otimes Y)(C \otimes Z),PQR}}V                                                              @VV{\phi_{ABC,(X \otimes P)(Y \otimes Q)(Z \otimes R)}}V \\
-- F ((A \otimes X) \otimes P)  ((B \otimes Y) \otimes Q) ((C \otimes Z) \otimes R)       @>>{F \alpha_{\mathcal{C_1}}} \alpha_{\mathcal{C_2}}\alpha_{\mathcal{C_3}}>   F (A \otimes (X \otimes P)) (B \otimes (Y \otimes Q)) (C \otimes (Z \otimes R)) \\
-- \end{CD}
-- \]
--
-- @
-- 'combine' 'Control.Category..' 'Control.Category.Tensor.grmap' 'Control.Category.Tensor.combine' 'Control.Category..' 'Control.Category.Tensor.bwd' 'Control.Category.Tensor.assoc' ≡ 'Data.Functor.fmap' ('Control.Category.Tensor.bwd' 'Control.Category.Tensor.assoc') 'Control.Category..' 'combine' 'Control.Category..' 'Control.Category.Tensor.glmap' 'combine'
-- @
class
  ( Associative cat tC1,
    Associative cat tC2,
    Associative cat tC3,
    Associative cat tD
  ) =>
  Semigroupal cat tC1 tC2 tC3 tD f
  where
  -- | A natural transformation \(\phi_{ABC,XYZ} : F\ A\ B\ C \bullet F\ X\ Y\ Z \to F\ (A \otimes X)\ (B \otimes Y) (C \otimes Z)\).
  combine :: tD (f x y z) (f x' y' z') `cat` f (tC1 x x') (tC2 y y') (tC3 z z')

infixr 9 |???|

(|???|) :: (Semigroupal (->) tC1 tC2 tC3 (,) p) => p a b c -> p a' b' c' -> p (a `tC1` a') (b `tC2` b') (c `tC3` c')
(|???|) = curry combine

infixr 9 |***|

(|***|) :: (Semigroupal (->) (,) (,) (,) (,) p) => p a b c -> p a' b' c' -> p (a, a') (b, b') (c, c')
(|***|) = curry combine

infixr 9 |**+|

(|**+|) :: (Semigroupal (->) (,) (,) Either (,) p) => p a b c -> p a' b' c' -> p (a, a') (b, b') (Either c c')
(|**+|) = curry combine

infixr 9 |**&|

(|**&|) :: (Semigroupal (->) (,) (,) These (,) p) => p a b c -> p a' b' c' -> p (a, a') (b, b') (These c c')
(|**&|) = curry combine

infixr 9 |*+*|

(|*+*|) :: (Semigroupal (->) (,) Either (,) (,) p) => p a b c -> p a' b' c' -> p (a, a') (Either b b') (c, c')
(|*+*|) = curry combine

infixr 9 |*++|

(|*++|) :: (Semigroupal (->) (,) Either Either (,) p) => p a b c -> p a' b' c' -> p (a, a') (Either b b') (Either c c')
(|*++|) = curry combine

infixr 9 |*+&|

(|*+&|) :: (Semigroupal (->) (,) Either These (,) p) => p a b c -> p a' b' c' -> p (a, a') (Either b b') (These c c')
(|*+&|) = curry combine

infixr 9 |*&*|

(|*&*|) :: (Semigroupal (->) (,) These (,) (,) p) => p a b c -> p a' b' c' -> p (a, a') (These b b') (c, c')
(|*&*|) = curry combine

infixr 9 |*&+|

(|*&+|) :: (Semigroupal (->) (,) These Either (,) p) => p a b c -> p a' b' c' -> p (a, a') (These b b') (Either c c')
(|*&+|) = curry combine

infixr 9 |*&&|

(|*&&|) :: (Semigroupal (->) (,) These These (,) p) => p a b c -> p a' b' c' -> p (a, a') (These b b') (These c c')
(|*&&|) = curry combine

infixr 9 |+**|

(|+**|) :: (Semigroupal (->) Either (,) (,) (,) p) => p a b c -> p a' b' c' -> p (Either a a') (b, b') (c, c')
(|+**|) = curry combine

infixr 9 |+*+|

(|+*+|) :: (Semigroupal (->) Either (,) Either (,) p) => p a b c -> p a' b' c' -> p (Either a a') (b, b') (Either c c')
(|+*+|) = curry combine

infixr 9 |+*&|

(|+*&|) :: (Semigroupal (->) Either (,) These (,) p) => p a b c -> p a' b' c' -> p (Either a a') (b, b') (These c c')
(|+*&|) = curry combine

infixr 9 |++*|

(|++*|) :: (Semigroupal (->) Either Either (,) (,) p) => p a b c -> p a' b' c' -> p (Either a a') (Either b b') (c, c')
(|++*|) = curry combine

infixr 9 |+++|

(|+++|) :: (Semigroupal (->) Either Either Either (,) p) => p a b c -> p a' b' c' -> p (Either a a') (Either b b') (Either c c')
(|+++|) = curry combine

infixr 9 |++&|

(|++&|) :: (Semigroupal (->) Either Either These (,) p) => p a b c -> p a' b' c' -> p (Either a a') (Either b b') (These c c')
(|++&|) = curry combine

infixr 9 |+&*|

(|+&*|) :: (Semigroupal (->) Either These (,) (,) p) => p a b c -> p a' b' c' -> p (Either a a') (These b b') (c, c')
(|+&*|) = curry combine

infixr 9 |+&+|

(|+&+|) :: (Semigroupal (->) Either These Either (,) p) => p a b c -> p a' b' c' -> p (Either a a') (These b b') (Either c c')
(|+&+|) = curry combine

infixr 9 |+&&|

(|+&&|) :: (Semigroupal (->) Either These These (,) p) => p a b c -> p a' b' c' -> p (Either a a') (These b b') (These c c')
(|+&&|) = curry combine

infixr 9 |&**|

(|&**|) :: (Semigroupal (->) These (,) (,) (,) p) => p a b c -> p a' b' c' -> p (These a a') (b, b') (c, c')
(|&**|) = curry combine

infixr 9 |&*+|

(|&*+|) :: (Semigroupal (->) These (,) Either (,) p) => p a b c -> p a' b' c' -> p (These a a') (b, b') (Either c c')
(|&*+|) = curry combine

infixr 9 |&*&|

(|&*&|) :: (Semigroupal (->) These (,) These (,) p) => p a b c -> p a' b' c' -> p (These a a') (b, b') (These c c')
(|&*&|) = curry combine

infixr 9 |&+*|

(|&+*|) :: (Semigroupal (->) These Either (,) (,) p) => p a b c -> p a' b' c' -> p (These a a') (Either b b') (c, c')
(|&+*|) = curry combine

infixr 9 |&++|

(|&++|) :: (Semigroupal (->) These Either Either (,) p) => p a b c -> p a' b' c' -> p (These a a') (Either b b') (Either c c')
(|&++|) = curry combine

infixr 9 |&+&|

(|&+&|) :: (Semigroupal (->) These Either These (,) p) => p a b c -> p a' b' c' -> p (These a a') (Either b b') (These c c')
(|&+&|) = curry combine

infixr 9 |&&*|

(|&&*|) :: (Semigroupal (->) These These (,) (,) p) => p a b c -> p a' b' c' -> p (These a a') (These b b') (c, c')
(|&&*|) = curry combine

infixr 9 |&&+|

(|&&+|) :: (Semigroupal (->) These These Either (,) p) => p a b c -> p a' b' c' -> p (These a a') (These b b') (Either c c')
(|&&+|) = curry combine

infixr 9 |&&&|

(|&&&|) :: (Semigroupal (->) These These These (,) p) => p a b c -> p a' b' c' -> p (These a a') (These b b') (These c c')
(|&&&|) = curry combine

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A trifunctor \(F : \mathcal{C_1} \times \mathcal{C_2} \times \mathcal{C_3} \to \mathcal{D}\) is 'Unital' if it supports a morphism
-- \(\phi : I_{\mathcal{D}} \to F\ I_{\mathcal{C_1}}\ I_{\mathcal{C_2}}\ I_{\mathcal{C_3}}\), which we call 'introduce'.
class Unital cat iC1 iC2 iC3 iD f where
  -- | @introduce@ maps from the identity in \(\mathcal{C_1} \times \mathcal{C_2} \times \mathcal{C_3}\) to the
  -- identity in \(\mathcal{D}\).
  introduce :: iD `cat` f iC1 iC2 iC3

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A trifunctor \(F : \mathcal{C_1} \times \mathcal{C_2} \times \mathcal{C_3} \to \mathcal{D}\) is 'Monoidal' if it maps between
-- \(\mathcal{C_1} \times \mathcal{C_2}\ \times \mathcal{C_3}\) and \(\mathcal{D}\) while preserving their monoidal structure.
-- Eg., a homomorphism of monoidal categories.
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
-- F A B C \bullet I_{\mathcal{D}}   @>{1 \bullet \phi}>>                                                            F A B \bullet F I_{\mathcal{C_{1}}} I_{\mathcal{C_{2}}} I_{\mathcal{C_{3}}}\\
-- @VV{\rho_{\mathcal{D}}}V                                                                                          @VV{\phi ABC,I_{\mathcal{C_{1}}}I_{\mathcal{C_{2}}}I_{\mathcal{C_{3}}}}V \\
-- F A B C                           @<<{F \rho_{\mathcal{C_{1}}} \rho_{\mathcal{C_{2}}} \rho_{\mathcal{C_{3}}}}<    F (A \otimes I_{\mathcal{C_{1}}}) (B \otimes I_{\mathcal{C_{2}}}) (C \otimes I_{\mathcal{C_{3}}})
-- \end{CD}
-- \]
--
-- @
-- 'combine' 'Control.Category..' 'Control.Category.Tensor.grmap' 'introduce' ≡ 'Control.Category.Tensor.bwd' 'Control.Category.Tensor.unitr' 'Control.Category..' 'Control.Category.Tensor.fwd' 'Control.Category.Tensor.unitr'
-- @
--
-- __ Left Unitality__:
--
-- \[
-- \begin{CD}
-- I_{\mathcal{D}} \bullet F A B C   @>{\phi \bullet 1}>>                                                                    F I_{\mathcal{C_{1}}} I_{\mathcal{C_{2}}} \bullet F A B C\\
-- @VV{\lambda_{\mathcal{D}}}V                                                                                               @VV{I_{\mathcal{C_{1}}}I_{\mathcal{C_{2}}}I_{\mathcal{C_{3}}},\phi ABC}V \\
-- F A B C                           @<<{F \lambda_{\mathcal{C_{1}}} \lambda_{\mathcal{C_{2}}} \lambda_{\mathcal{C_{3}}}}<   F (I_{\mathcal{C_{1}}} \otimes A) (I_{\mathcal{C_{2}}} \otimes B) (I_{\mathcal{C_{3}}} \otimes C)
-- \end{CD}
-- \]
--
-- @
-- 'combine' 'Control.Category..' 'Control.Category.Tensor.glmap' 'introduce' ≡ 'Data.Functor.fmap' ('Control.Category.Tensor.bwd' 'Control.Category.Tensor.unitl') 'Control.Category..' 'Control.Category.Tensor.fwd' 'Control.Category.Tensor.unitl'
-- @
class
  ( Tensor cat tC1 iC1,
    Tensor cat tC2 iC2,
    Tensor cat tC3 iC3,
    Tensor cat tD iD,
    Semigroupal cat tC1 tC2 tC3 tD f,
    Unital cat iC1 iC2 iC3 iD f
  ) =>
  Monoidal cat tC1 iC1 tC2 iC2 tC3 iC3 tD iD f
