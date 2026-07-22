-- | Reusable @hedgehog-classes@ 'Laws' for the structures in
-- "Control.Category.Tensor" — 'GBifunctor', 'Iso', 'Associative', 'Tensor', and
-- 'Symmetric' — so a consumer can law-test their own instances the same way they
-- test 'Monoid' or 'Applicative':
--
-- > import Control.Category.Tensor.Laws (associativeLaws)
-- > import Hedgehog.Classes (lawsCheck)
-- >
-- > main :: IO Bool
-- > main = lawsCheck (associativeLaws runKleisli genTheseTensor)
--
-- Each law is checked extensionally through a caller-supplied observer (see
-- 'Control.Category.Laws.Internal.agree'). Every law here reduces to \"an
-- endomorphism agrees with 'id'\" — the round-trips of an 'Iso', the iso-ness of
-- @assoc@ \/ @unitl@ \/ @unitr@, the involution of @swap@, the functoriality of
-- @gbimap@ — so the observer only ever runs /endomorphisms/ @cat z z@, and a
-- single @forall z. cat z z -> z -> obs z@ serves every category (including
-- 'Op', which a forward observer could not).
module Control.Category.Tensor.Laws
  ( -- * GBifunctor
    gbifunctorLaws,

    -- * Iso
    isoLaws,

    -- * Associative
    associativeLaws,

    -- * Tensor
    tensorLaws,

    -- * Symmetric
    symmetricLaws,
  )
where

--------------------------------------------------------------------------------

import Control.Category (Category, id, (>>>))
import Control.Category.Laws.Internal (agree, genBool, genInt)
import Control.Category.Tensor
  ( Associative (assoc),
    GBifunctor (gbimap),
    Iso (..),
    Symmetric (swap),
    Tensor (unitl, unitr),
    glmap,
    grmap,
  )
import Hedgehog (Gen, Property)
import Hedgehog.Classes (Laws (..))
import Prelude hiding (id)

--------------------------------------------------------------------------------

-- | The two isomorphism laws for an 'Iso': @fwd . bwd ≡ id@ and
-- @bwd . fwd ≡ id@. Shared by 'isoLaws', 'associativeLaws', and 'tensorLaws'.
isoProperties ::
  forall cat obs a b.
  ( Category cat,
    Show a,
    Show b,
    Eq (obs a),
    Show (obs a),
    Eq (obs b),
    Show (obs b)
  ) =>
  (forall z. cat z z -> z -> obs z) ->
  Iso cat a b ->
  Gen a ->
  Gen b ->
  [(String, Property)]
isoProperties run iso genA genB =
  [ ("fwd . bwd = id", agree run (bwd iso >>> fwd iso) id genB),
    ("bwd . fwd = id", agree run (fwd iso >>> bwd iso) id genA)
  ]

--------------------------------------------------------------------------------
-- GBifunctor

-- | The 'GBifunctor' laws for @gbimap@ in category @cat@ at tensor @t@:
--
-- @
-- 'gbimap' 'id' 'id'                    ≡ 'id'
-- 'gbimap' (f '>>>' f') (g '>>>' g')        ≡ 'gbimap' f g '>>>' 'gbimap' f' g'
-- 'gbimap' f g                      ≡ 'grmap' g '>>>' 'glmap' f
-- @
--
-- The two arrow pairs are endomorphisms on each tensor factor: @(f, f')@ on the
-- left factor @a@ and @(g, g')@ on the right factor @c@.
gbifunctorLaws ::
  forall cat t obs a c.
  ( GBifunctor cat cat cat t,
    Show (t a c),
    Eq (obs (t a c)),
    Show (obs (t a c))
  ) =>
  (forall z. cat z z -> z -> obs z) ->
  (cat a a, cat a a) ->
  (cat c c, cat c c) ->
  Gen (t a c) ->
  Laws
gbifunctorLaws run (f, f') (g, g') gen =
  Laws
    "GBifunctor"
    [ ("Identity", agree run (gbimap id id) id gen),
      ("Composition", agree run (gbimap (f >>> f') (g >>> g')) (gbimap f g >>> gbimap f' g') gen),
      ("Decomposition", agree run (gbimap f g) (grmap g >>> glmap f) gen)
    ]

--------------------------------------------------------------------------------
-- Iso

-- | The isomorphism laws for a given 'Iso' value: @fwd@ and @bwd@ are mutually
-- inverse, checked on generated inhabitants of both endpoints.
isoLaws ::
  forall cat obs a b.
  ( Category cat,
    Show a,
    Show b,
    Eq (obs a),
    Show (obs a),
    Eq (obs b),
    Show (obs b)
  ) =>
  (forall z. cat z z -> z -> obs z) ->
  Iso cat a b ->
  Gen a ->
  Gen b ->
  Laws
isoLaws run iso genA genB = Laws "Iso" (isoProperties run iso genA genB)

--------------------------------------------------------------------------------
-- Associative

-- | The 'Associative' laws: @assoc@ is an isomorphism between the two
-- re-nestings of @t@. @genT@ builds a tensor from generators for its factors
-- (e.g. @\\gx gy -> (,) '<$>' gx '<*>' gy@ for @(,)@), from which the nested
-- witnesses are assembled.
associativeLaws ::
  forall cat t obs.
  ( Associative cat t,
    Show (t Int (t Int Int)),
    Show (t (t Int Int) Int),
    Eq (obs (t Int (t Int Int))),
    Show (obs (t Int (t Int Int))),
    Eq (obs (t (t Int Int) Int)),
    Show (obs (t (t Int Int) Int))
  ) =>
  (forall z. cat z z -> z -> obs z) ->
  (forall x y. Gen x -> Gen y -> Gen (t x y)) ->
  Laws
associativeLaws run genT =
  Laws
    "Associative"
    ( isoProperties
        run
        (assoc @cat @t)
        (genT genInt (genT genInt genInt))
        (genT (genT genInt genInt) genInt)
    )

--------------------------------------------------------------------------------
-- Tensor

-- | The 'Tensor' laws: the left and right unitors @unitl@ \/ @unitr@ are
-- isomorphisms. The caller supplies generators for @i \`t\` a@ and @a \`t\` i@
-- (with @a = 'Int'@), which also fixes the unit @i@ — needed because some units
-- ('Data.Void.Void') are uninhabited and cannot be generated directly.
tensorLaws ::
  forall cat t i obs.
  ( Tensor cat t i,
    Show (t i Int),
    Show (t Int i),
    Eq (obs Int),
    Show (obs Int),
    Eq (obs (t i Int)),
    Show (obs (t i Int)),
    Eq (obs (t Int i)),
    Show (obs (t Int i))
  ) =>
  (forall z. cat z z -> z -> obs z) ->
  Gen (t i Int) ->
  Gen (t Int i) ->
  Laws
tensorLaws run genIA genAI =
  Laws
    "Tensor"
    ( prefixed "unitl" (isoProperties run (unitl @cat @t) genIA genInt)
        ++ prefixed "unitr" (isoProperties run (unitr @cat @t) genAI genInt)
    )
  where
    prefixed p = map (\(n, pr) -> (p <> " " <> n, pr))

--------------------------------------------------------------------------------
-- Symmetric

-- | The 'Symmetric' law: @swap@ is its own inverse, @swap ≡ swap⁻¹@, checked at
-- distinct factor types (@Int@, @Bool@) so a non-swapping @swap@ cannot pass.
symmetricLaws ::
  forall cat t obs.
  ( Symmetric cat t,
    Show (t Int Bool),
    Eq (obs (t Int Bool)),
    Show (obs (t Int Bool))
  ) =>
  (forall z. cat z z -> z -> obs z) ->
  (forall x y. Gen x -> Gen y -> Gen (t x y)) ->
  Laws
symmetricLaws run genT =
  Laws
    "Symmetric"
    [("swap . swap = id", agree run (swap @cat @t >>> swap @cat @t) id (genT genInt genBool))]
