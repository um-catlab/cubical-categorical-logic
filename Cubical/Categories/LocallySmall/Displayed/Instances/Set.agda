module Cubical.Categories.LocallySmall.Displayed.Instances.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Set
open import Cubical.Categories.LocallySmall.Constructions.BinProduct

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total

open Category
open Categoryᴰ
open Σω

-- SETᴰ over ∫SET × LEVEL
SETᴰ' :
  SmallFibersCategoryᴰ (∫C SET ×C LEVEL) _
    (λ ((liftω ℓ , liftω A) , liftω ℓ') → ⟨ A ⟩ → hSet ℓ')
    _
SETᴰ' .Hom[_][_,_] ((_ , f), _) (liftω A) (liftω B) =
  ∀ x → ⟨ A x ⟩ → ⟨ B (f x) ⟩
SETᴰ' .idᴰ = λ x z → z
SETᴰ' ._⋆ᴰ_ {f = ((_ , f), _)} {((_ , g), _)}
  fᴰ gᴰ x xᴰ = gᴰ (f x) (fᴰ x xᴰ)
SETᴰ' .⋆IdLᴰ _ = refl
SETᴰ' .⋆IdRᴰ _ = refl
SETᴰ' .⋆Assocᴰ _ _ _ = refl
SETᴰ' .isSetHomᴰ {yᴰ = liftω B} = isSetΠ2 (λ _ _ → B _ .snd)

-- Reorganize the base category
-- Instead of the total category of (SET over LEVEL) paired with LEVEL,
-- directly display SET over LEVEL × LEVEL
weakenLevelSET : SmallFibersCategoryᴰ (LEVEL ×C LEVEL) _ _ _
weakenLevelSET = reindexEqSF (π₁ LEVEL LEVEL) SET Eq.refl λ _ _ → Eq.refl

module _ (ℓ ℓ' : Level) where
  private
    module SET = CategoryᴰNotation SET
    module weakenLevelSET = CategoryᴰNotation weakenLevelSET
  open Functor
  SET→weakenLevelSET : Functor SET.v[ liftω ℓ ] weakenLevelSET.v[ liftω ℓ , liftω ℓ' ]
  SET→weakenLevelSET .F-ob = λ z → z
  SET→weakenLevelSET .F-hom = λ z → z
  SET→weakenLevelSET .F-id = refl
  SET→weakenLevelSET .F-seq _ _ = refl

-- SETᴰ over ∫weakenLevelSET
SETᴰ'' :
  SmallFibersCategoryᴰ (∫C weakenLevelSET) _
    (λ ((liftω ℓ , liftω ℓ') , liftω A) → ⟨ A ⟩ → hSet ℓ')
    _
SETᴰ'' .Hom[_][_,_] (_ , f) (liftω A) (liftω B) =
  ∀ x → ⟨ A x ⟩ → ⟨ B (f x) ⟩
SETᴰ'' .idᴰ = λ _ z → z
SETᴰ'' ._⋆ᴰ_ {f = (_ , f)} fᴰ gᴰ x xᴰ = gᴰ (f x) (fᴰ x xᴰ)
SETᴰ'' .⋆IdLᴰ _ = refl
SETᴰ'' .⋆IdRᴰ _ = refl
SETᴰ'' .⋆Assocᴰ _ _ _ = refl
SETᴰ'' .isSetHomᴰ {yᴰ = liftω B} = isSetΠ2 λ _ _ → B _ .snd

-- SETᴰ over LEVEL × LEVEL
-- Downstairs: (ℓ , ℓ') : Level × Level
-- Upstairs: (A , B) : Σ[ A ∈ hSet ℓ ] (⟨ A ⟩ → hSet ℓ')
SETᴰ : SmallFibersCategoryᴰ (LEVEL ×C LEVEL) _ _ _
SETᴰ = ∫CᴰSF weakenLevelSET SETᴰ''

module ∫CᴰSETᴰNotation = ∫CᴰSFNotation weakenLevelSET SETᴰ''
