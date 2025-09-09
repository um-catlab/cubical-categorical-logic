module Cubical.Categories.Displayed.Instances.Terminal.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Instances.Terminal as Terminal
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Fibration.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Section
open Functorᴰ
open UniversalElementⱽ

module _ {C : Category ℓC ℓC'} where
  isFibrationUnitᴰ : isFibration (Unitᴰ C)
  isFibrationUnitᴰ cᴰ p .vertexⱽ = tt
  isFibrationUnitᴰ cᴰ p .elementⱽ = tt
  isFibrationUnitᴰ cᴰ p .universalⱽ .fst = λ _ → tt
  isFibrationUnitᴰ cᴰ p .universalⱽ .snd .fst = λ _ → refl
  isFibrationUnitᴰ cᴰ p .universalⱽ .snd .snd = λ _ → refl

  -- module _ (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  --   preservesCartesianLiftsIntro :
  --     PreservesCartesianLifts {Cᴰ = Cᴰ} (Terminal.introF Id)
  --   preservesCartesianLiftsIntro _ _ _ _ _ _ _ _ = uniqueExists _
  --     refl
  --     (λ _ → isSetUnit _ _)
  --     λ _ _ → refl
