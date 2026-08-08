{-
  DISPLAYED SETS OVER LEVEL, forded -- with no bookkeeping.

  Compare Sets.Base's `SET`.  The point of this file is what is
  ABSENT.  `LEVEL` is `Indiscrete (Liftω Level)`, so its homs are
  `Unit`; consequently `Hom[ f ][ X , Y ]` here does not mention `f`
  at all.  That means:

    * the ford arguments (`i`, `ei`, `f`, `g`, `h`, `e`) are ignored
      outright -- fording costs literally nothing at the level layer;
    * every law is `refl`, including the two ford coherences, since
      `λ k → Hom[ p k ][ _ , _ ]` is a constant family;
    * and `reindexS` (Displayed.Category.Forded) is then strictly
      functorial on it, so moving between LEVEL, `LEVEL ×  LEVEL` and
      the various fibres composes definitionally.  (The `Id⋆Eq`
      witness a fibre needs does not disappear -- see
      SmallDisplayedFibers.Forded for the honest accounting -- but
      every step still COMPUTES, because the fords are `Eq`-valued and
      `Eq.transport C Eq.refl b` reduces to `b`.)

  This is the layer Categoryᴰ's `Homᴰ[_,_]` was hand-rolled for; here
  it falls out of the general definition.
-}
module Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Functor.Strict
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Forded
open import Cubical.Categories.LocallySmall.Variables.Base

open Categoryᶠᴰ
open Liftω

-- `GloballySmallCategory Cob ℓ` is a synonym for `Category Cob (λ _ _ → ℓ)`,
-- so LEVEL is already a Category.
LEVELᶜ : Category (Liftω Level) _
LEVELᶜ = LEVEL

-- A SET AT A LEVEL, displayed over LEVEL.  Note that not one field
-- mentions its ford arguments.
SETᶠ : Categoryᶠᴰ LEVELᶜ (λ ℓ → Liftω (hSet (ℓ .lowerω)))
  (λ ℓ ℓ' _ _ → ℓ-max (ℓ .lowerω) (ℓ' .lowerω))
SETᶠ .Hom[_][_,_] _ (liftω X) (liftω Y) = ⟨ X ⟩ → ⟨ Y ⟩
SETᶠ .idᴰ _ _ = λ x → x
SETᶠ .⋆ᴰ _ _ _ _ fᴰ gᴰ = λ x → gᴰ (fᴰ x)
SETᶠ .⋆IdLᴰ _ _ _ _ _ = refl
SETᶠ .⋆IdRᴰ _ _ _ _ _ = refl
SETᶠ .⋆Assocᴰ _ _ _ _ _ _ _ _ _ _ _ _ _ = refl
SETᶠ .idᴰ-coh _ _ _ _ _ = refl
SETᶠ .⋆ᴰ-coh _ _ _ _ _ _ _ _ _ = refl
SETᶠ .isSetHomᴰ {yᴰ = liftω Y} = isSet→ (Y .snd)

-- the total category: pairs (ℓ , a set at ℓ), with `Fstᶠ` its strict
-- display map back to LEVEL.
SETTOT : Category _ _
SETTOT = ∫ᶠ SETᶠ

SETTOT→LEVEL : StrictFunctor SETTOT LEVELᶜ
SETTOT→LEVEL = Fstᶠ SETᶠ

-- (`weakenᶠ`, which adds a SECOND level without `weaken LEVEL LEVEL`
-- and its nested Σω, is generic and lives in Displayed.Category.Forded.)

-- ------------------------------------------------------------------
-- THE TELESCOPE, with no bookkeeping.  Objects of `LEVEL-SET-LEVEL`
-- are (ℓ , X : hSet ℓ , ℓ'), built by two extensions and no `weaken
-- LEVEL LEVEL`, no `fibEq`, no `Eq.refl`.
LEVEL-SET-LEVEL : Category _ _
LEVEL-SET-LEVEL = ∫ᶠ (weakenᶠ SETTOT LEVELᶜ)

-- and the display maps compose STRICTLY, by _S∘_
LEVEL-SET-LEVEL→LEVEL : StrictFunctor LEVEL-SET-LEVEL LEVELᶜ
LEVEL-SET-LEVEL→LEVEL = SETTOT→LEVEL S∘ Fstᶠ (weakenᶠ SETTOT LEVELᶜ)

-- ------------------------------------------------------------------
-- THE EXISTING INSTANCES LIFT FOR FREE.  `SmallFibersCategoryᴰ` and
-- `SmallFibersᴰCategoryᴰ` are synonyms for `Categoryᴰ`, so
-- `fromCategoryᴰ` applies to Sets.Base's `SET` and `SETᴰ` directly --
-- the families layer, which is where the telescope bookkeeping lived,
-- arrives forded with nothing re-proved.
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base
  using (SET; SETᴰ)

SETᶠ' : Categoryᶠᴰ LEVELᶜ _ _
SETᶠ' = fromCategoryᴰ SET

SETᴰᶠ : Categoryᶠᴰ _ _ _
SETᴰᶠ = fromCategoryᴰ SETᴰ

-- and reindexing the lifted families layer is strictly functorial:
-- inhabited by the identity, so the two sides are definitionally equal.
SETᴰᶠ-reindex-Id : Coe (reindexS SId SETᴰᶠ) SETᴰᶠ
SETᴰᶠ-reindex-Id P x = x

SETᶠ-reindex-Id : Coe (reindexS SId SETᶠ) SETᶠ
SETᶠ-reindex-Id P x = x
