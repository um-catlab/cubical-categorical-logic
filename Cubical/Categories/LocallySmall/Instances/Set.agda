module Cubical.Categories.LocallySmall.Instances.Set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Displayed.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level

open Category
open Categoryᴰ
open Σω

SET : SmallFibersCategoryᴰ LEVEL _ (λ (liftω ℓ) → hSet ℓ) _
SET .Hom[_][_,_] _ (liftω X) (liftω Y) = ⟨ X ⟩ → ⟨ Y ⟩
SET .idᴰ = λ z → z
SET ._⋆ᴰ_ = λ g f x → f (g x)
SET .⋆IdLᴰ = λ _ → refl
SET .⋆IdRᴰ = λ _ → refl
SET .⋆Assocᴰ = λ _ _ _ → refl
SET .isSetHomᴰ {yᴰ = (liftω Y)} = isSet→ (Y .snd)
