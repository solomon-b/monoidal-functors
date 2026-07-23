{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Reusable @hedgehog-classes@ 'Laws' for the classes in
-- "Control.Category.Cartesian" — 'Semicartesian', 'Semicocartesian',
-- 'Cartesian', and 'Cocartesian' — so a consumer can law-test their own
-- instances the same way they test 'Monoid' or 'Applicative':
--
-- > import Control.Category.Cartesian.Laws (cartesianLaws)
-- > import Hedgehog.Classes (lawsCheck)
-- >
-- > main :: IO Bool
-- > main = lawsCheck (cartesianLaws @(->) @(,) @() (\f -> Identity . f))
--
-- As in "Control.Category.Tensor.Laws", morphisms here have no 'Eq' \/ 'Show',
-- so every law is checked /extensionally/ through a caller-supplied observer
-- @run@. The observer's shape follows the law:
--
--   * the diagonal \/ codiagonal coassociativity laws ('Semicartesian' \/
--     'Semicocartesian') relate morphisms whose domain and codomain /differ/, so
--     they take a general @forall x y. cat x y -> x -> obs y@ observer — usable
--     for @('->')@, @'Star' m@, @'Kleisli' m@, but not 'Op';
--   * the projection \/ inclusion unit laws ('Cartesian' \/ 'Cocartesian') relate
--     /endomorphisms/ against 'id', so they take a
--     @forall z. cat z z -> z -> obs z@ observer — which additionally covers 'Op'.
module Control.Category.Cartesian.Laws
  ( -- * Semicartesian
    semicartesianLaws,

    -- * Semicocartesian
    semicocartesianLaws,

    -- * Cartesian
    cartesianLaws,

    -- * Cocartesian
    cocartesianLaws,
  )
where

--------------------------------------------------------------------------------

import Control.Category (id, (>>>))
import Control.Category.Cartesian
  ( Cartesian (kill),
    Cocartesian (spawn),
    Semicartesian (split),
    Semicocartesian (merge),
  )
import Control.Category.Laws.Internal (agree, genInt)
import Control.Category.Tensor
  ( Associative (assoc),
    Iso (bwd, fwd),
    Tensor (unitl, unitr),
    glmap,
    grmap,
  )
import Hedgehog (Gen)
import Hedgehog.Classes (Laws (..))
import Prelude hiding (id)

--------------------------------------------------------------------------------
-- Semicartesian

-- | The 'Semicartesian' laws: the diagonal 'split' is coassociative.
--
-- @
-- 'Control.Category.Tensor.grmap' 'split' '>>>' … ≡ 'split' '>>>' 'Control.Category.Tensor.glmap' 'split' '>>>' 'bwd' 'assoc'
-- @
semicartesianLaws ::
  forall cat t obs.
  ( Semicartesian cat t,
    Eq (obs (t Int (t Int Int))),
    Show (obs (t Int (t Int Int))),
    Eq (obs (t (t Int Int) Int)),
    Show (obs (t (t Int Int) Int))
  ) =>
  (forall x y. cat x y -> x -> obs y) ->
  Laws
semicartesianLaws run =
  Laws
    "Semicartesian"
    [ ("split coassociativity (right)", agree run (s >>> grmap s) (s >>> glmap s >>> bwd assoc) genInt),
      ("split coassociativity (left)", agree run (s >>> glmap s) (s >>> grmap s >>> fwd assoc) genInt)
    ]
  where
    s :: cat Int (t Int Int)
    s = split

--------------------------------------------------------------------------------
-- Semicocartesian

-- | The 'Semicocartesian' laws: the codiagonal 'merge' is coassociative. @genT@
-- builds a tensor from generators for its factors, supplying the nested inputs.
semicocartesianLaws ::
  forall cat t obs.
  ( Semicocartesian cat t,
    Show (t Int (t Int Int)),
    Show (t (t Int Int) Int),
    Eq (obs Int),
    Show (obs Int)
  ) =>
  (forall x y. cat x y -> x -> obs y) ->
  (forall x y. Gen x -> Gen y -> Gen (t x y)) ->
  Laws
semicocartesianLaws run genT =
  Laws
    "Semicocartesian"
    [ ("merge coassociativity (right)", agree run (grmap m >>> m) (fwd assoc >>> glmap m >>> m) (genT genInt (genT genInt genInt))),
      ("merge coassociativity (left)", agree run (glmap m >>> m) (bwd assoc >>> grmap m >>> m) (genT (genT genInt genInt) genInt))
    ]
  where
    m :: cat (t Int Int) Int
    m = merge

--------------------------------------------------------------------------------
-- Cartesian

-- | The 'Cartesian' laws: 'kill' is a counit for 'split', so projecting after
-- duplicating is the identity.
--
-- @
-- 'fwd' 'unitl' '.' 'Control.Category.Tensor.glmap' 'kill' '.' 'split' ≡ 'id'
-- 'fwd' 'unitr' '.' 'Control.Category.Tensor.grmap' 'kill' '.' 'split' ≡ 'id'
-- @
cartesianLaws ::
  forall cat t i obs.
  ( Cartesian cat t i,
    Eq (obs Int),
    Show (obs Int)
  ) =>
  (forall z. cat z z -> z -> obs z) ->
  Laws
cartesianLaws run =
  Laws
    "Cartesian"
    [ ("left projection", agree run (split @cat @t >>> glmap (kill @cat @t @i) >>> fwd (unitl @cat @t @i)) id genInt),
      ("right projection", agree run (split @cat @t >>> grmap (kill @cat @t @i) >>> fwd (unitr @cat @t @i)) id genInt)
    ]

--------------------------------------------------------------------------------
-- Cocartesian

-- | The 'Cocartesian' laws: 'spawn' is a unit for 'merge', so merging after
-- including is the identity.
--
-- @
-- 'merge' '.' 'Control.Category.Tensor.glmap' 'spawn' '.' 'bwd' 'unitl' ≡ 'id'
-- 'merge' '.' 'Control.Category.Tensor.grmap' 'spawn' '.' 'bwd' 'unitr' ≡ 'id'
-- @
cocartesianLaws ::
  forall cat t i obs.
  ( Cocartesian cat t i,
    Eq (obs Int),
    Show (obs Int)
  ) =>
  (forall z. cat z z -> z -> obs z) ->
  Laws
cocartesianLaws run =
  Laws
    "Cocartesian"
    [ ("left inclusion", agree run (bwd (unitl @cat @t @i) >>> glmap (spawn @cat @t @i) >>> merge @cat @t) id genInt),
      ("right inclusion", agree run (bwd (unitr @cat @t @i) >>> grmap (spawn @cat @t @i) >>> merge @cat @t) id genInt)
    ]
