module Cubical.Categories.Displayed.Instances.Family.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓ ℓ' ℓC ℓC' : Level

open Category
open Categoryᴰ
module _ {ℓ} (C : Category ℓC ℓC') where
  private
    module C = Category C
  Fam : Categoryᴰ (SET ℓ) (ℓ-max ℓC ℓ) (ℓ-max ℓC' ℓ)
  Fam .ob[_] X = ⟨ X ⟩ → C .ob
  Fam .Hom[_][_,_] f xᴰ yᴰ = ∀ x → C [ xᴰ x , yᴰ (f x) ]
  Fam .idᴰ x = C .id
  Fam ._⋆ᴰ_ fᴰ gᴰ x = fᴰ _ C.⋆ gᴰ _
  Fam .⋆IdLᴰ fᴰ = funExt (λ x₁ → C.⋆IdL _)
  Fam .⋆IdRᴰ fᴰ = funExt (λ x → C.⋆IdR _)
  Fam .⋆Assocᴰ fᴰ gᴰ hᴰ = funExt (λ x → C.⋆Assoc _ _ _)
  Fam .isSetHomᴰ = isSetΠ (λ _ → C.isSetHom)
