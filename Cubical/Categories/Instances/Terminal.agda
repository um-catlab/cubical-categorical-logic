{-# OPTIONS --safe #-}
module Cubical.Categories.Instances.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Categories.Category.Base

UnitC : Category ℓ-zero ℓ-zero
UnitC .Category.ob = Unit
UnitC .Category.Hom[_,_] _ _ = Unit
UnitC .Category.id = tt
UnitC .Category._⋆_ = λ f g → tt
UnitC .Category.⋆IdL = λ _ → refl
UnitC .Category.⋆IdR = λ _ → refl
UnitC .Category.⋆Assoc = λ _ _ _ → refl
UnitC .Category.isSetHom = λ x₁ y₁ x₂ y₂ i i₁ → tt

UnitC* : ∀ ℓ ℓ' → Category ℓ ℓ'
UnitC* ℓ ℓ' .Category.ob = Unit* {ℓ}
UnitC* ℓ ℓ' .Category.Hom[_,_] x y = Unit* {ℓ'}
UnitC* ℓ ℓ' .Category.id = tt*
UnitC* ℓ ℓ' .Category._⋆_ = λ f g → tt*
UnitC* ℓ ℓ' .Category.⋆IdL f i = tt*
UnitC* ℓ ℓ' .Category.⋆IdR f i = tt*
UnitC* ℓ ℓ' .Category.⋆Assoc f g h i = tt*
UnitC* ℓ ℓ' .Category.isSetHom x y x₁ y₁ i i₁ = tt*
