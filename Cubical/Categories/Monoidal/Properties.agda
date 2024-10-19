{-# OPTIONS --safe #-}

module Cubical.Categories.Monoidal.Properties where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
open Category
open Functor
open isIso
open NatTrans
open NatIso
module _ (M : MonoidalCategory ℓC ℓC') where
  private
    module M = MonoidalCategory M

  ⊗id-cancel : ∀ {x y : M.ob}
    → {f g : M.C [ x , y ]}
    → (f M.⊗ₕ M.id {M.unit}) ≡ (g M.⊗ₕ M.id)
    → f ≡ g
  ⊗id-cancel p =
    ⋆CancelL (NatIsoAt M.ρ _)
      (sym (M.ρ .trans .N-hom _)
      ∙ cong₂ M._⋆_ p refl
      ∙ M.ρ .trans .N-hom _)

  triangle' : ∀ x y →
    (M.ρ⟨ x ⟩ M.⊗ₕ M.id) ≡ (M.α⁻¹⟨ x , M.unit , y ⟩ M.⋆ (M.id M.⊗ₕ M.η⟨ y ⟩))
  triangle' x y = ⋆InvLMove (NatIsoAt M.α _) (M.triangle x y)
