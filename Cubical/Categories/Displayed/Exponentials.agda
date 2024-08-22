{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Fibration.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Category
open UniversalElement
open Functorᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (isFib : AllCartesianOvers Cᴰ) {- for typechecking performance -}
  (vps : VerticalBinProducts Cᴰ)
  where
  open CartesianOver
  private
    module Cᴰ = Categoryᴰ Cᴰ
  module _ {c : C .ob}
    (cᴰ cᴰ' : Cᴰ.ob[ c ]) where
    VerticalExponentialsAt : (cᴰ'' : Cᴰ.ob[ c ]) → Type _
    VerticalExponentialsAt cᴰ'' = UniversalElementᴰ Cᴰ Pᴰ idue
      where
      -- TODO: this is already in the library, I just don't want to find it right now
      idue : UniversalElement C (C [-, c ])
      idue .vertex = c
      idue .element = C .id
      idue .universal c' .equiv-proof f = uniqueExists
        f (C .⋆IdR _) (λ _ → C .isSetHom _ _) (λ _ p → sym p ∙ C .⋆IdR _)
      Pᴰ : Presheafᴰ Cᴰ (C [-, c ]) _
      Pᴰ .F-obᴰ {x = c'} c'ᴰ f = Cᴰ.Hom[ f ][ c'ᴰ∧f*cᴰ.vert , cᴰ' ] , Cᴰ.isSetHomᴰ
        where
        module c'ᴰ∧f*cᴰ = VerticalBinProductsAtNotation (vps (c'ᴰ , isFib cᴰ f .f*cᴰ'))
      Pᴰ .F-homᴰ {x = c'} {y = c''} {f = g} {xᴰ = c'ᴰ} {yᴰ = c''ᴰ} gᴰ f fᴰ =
        c'ᴰ∧f*cᴰ.⟨
          rect (c''ᴰ∧gf*cᴰ.π₁ Cᴰ.⋆ᴰ gᴰ) ,
          rect (c''ᴰ∧gf*cᴰ.π₂ Cᴰ.⋆ᴰ isFib cᴰ f .isCartesian _ g (isFib cᴰ (g ⋆⟨ C ⟩ f) .π) .fst .fst)
        ⟩ Cᴰ.⋆ᴰ fᴰ
        where
        module c'ᴰ∧f*cᴰ = VerticalBinProductsAtNotation (vps (c'ᴰ , isFib cᴰ f .f*cᴰ'))
        module c''ᴰ∧gf*cᴰ = VerticalBinProductsAtNotation (vps (c''ᴰ , (isFib cᴰ (g ⋆⟨ C ⟩ f) .f*cᴰ')))
        rect : ∀{x yᴰ zᴰ} → Cᴰ.Hom[ C .id ⋆⟨ C ⟩ x ][ yᴰ , zᴰ ] → Cᴰ.Hom[ x ⋆⟨ C ⟩ C .id ][ yᴰ , zᴰ ]
        rect = transport (congS (λ x → Cᴰ.Hom[ x ][ _ , _ ] ) (C .⋆IdL _ ∙ sym (C .⋆IdR _)))
      Pᴰ .F-idᴰ = {!!}
      Pᴰ .F-seqᴰ = {!!}
