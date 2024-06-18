{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open UniversalElementᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓD ℓD') where
  private module Cᴰ = Categoryᴰ Cᴰ
  LiftedBinProduct : ∀ {c12} → BinProduct' C c12
              → (Cᴰ.ob[ c12 .fst ] × Cᴰ.ob[ c12 .snd ])
              → Type _
  LiftedBinProduct = RightAdjointAtᴰ (ΔCᴰ Cᴰ)

  LiftedBinProducts : BinProducts' C → Type _
  LiftedBinProducts = RightAdjointᴰ (ΔCᴰ Cᴰ)

  VerticalBinProductsAt : ∀ {c} → (Cᴰ.ob[ c ] × Cᴰ.ob[ c ]) → Type _
  VerticalBinProductsAt = VerticalRightAdjointAtᴰ (Δᴰ Cᴰ)

  VerticalBinProducts : Type _
  VerticalBinProducts = VerticalRightAdjointᴰ (Δᴰ Cᴰ)

module _ {C  : Category ℓC ℓC'}{c : C .ob}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private module Cᴰ = Categoryᴰ Cᴰ
  -- meant to be used as `module cᴰ∧cᴰ' = VerticalBinProductsAtNotation vbp`
  module VerticalBinProductsAtNotation {cᴰ cᴰ' : Cᴰ.ob[ c ]}
    (vbp : VerticalBinProductsAt Cᴰ (cᴰ , cᴰ')) where

    vert : Cᴰ.ob[ c ]
    vert = vbp .vertexᴰ

    -- shorthand for terminal vertical cone
    π₁₂ :
      Cᴰ.Hom[ C .id ][ vert , cᴰ ] × Cᴰ.Hom[ C .id ][ vert , cᴰ' ]
    π₁₂ = vbp .elementᴰ
    π₁ = π₁₂ .fst
    π₂ = π₁₂ .snd

    module _ {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{f : C [ x , c ]} where
      ⟨_,_⟩ : Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ ] →
        Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ' ] →
        Cᴰ.Hom[ f ][ xᴰ , vert ]
      ⟨ fᴰ , fᴰ' ⟩ = invIsEq (vbp .universalᴰ) (fᴰ , fᴰ')

      ⟨_,_⟩' : Cᴰ.Hom[ f ][ xᴰ , cᴰ ] →
        Cᴰ.Hom[ f ][ xᴰ , cᴰ' ] →
        Cᴰ.Hom[ f ][ xᴰ , vert ]
      ⟨ fᴰ , fᴰ' ⟩' = ⟨ fᴰ Cᴰ.⋆ᴰ Cᴰ.idᴰ , fᴰ' Cᴰ.⋆ᴰ Cᴰ.idᴰ ⟩

      β : (fᴰ : Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ ]) →
        (fᴰ' : Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ' ]) →
        (⟨ fᴰ , fᴰ' ⟩ Cᴰ.⋆ᴰ π₁ , ⟨ fᴰ , fᴰ' ⟩ Cᴰ.⋆ᴰ π₂) ≡
        (fᴰ , fᴰ')
      β fᴰ fᴰ' = secIsEq (vbp .universalᴰ) (fᴰ , fᴰ')

      β' : (fᴰ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ]) →
        (fᴰ' : Cᴰ.Hom[ f ][ xᴰ , cᴰ' ]) →
        (⟨ fᴰ , fᴰ' ⟩' Cᴰ.⋆ᴰ π₁ , ⟨ fᴰ , fᴰ' ⟩' Cᴰ.⋆ᴰ π₂) ≡
        (fᴰ Cᴰ.⋆ᴰ Cᴰ.idᴰ , fᴰ' Cᴰ.⋆ᴰ Cᴰ.idᴰ)
      β' fᴰ fᴰ' = β (fᴰ Cᴰ.⋆ᴰ Cᴰ.idᴰ) (fᴰ' Cᴰ.⋆ᴰ Cᴰ.idᴰ)

      η : (fᴰ'' : Cᴰ.Hom[ f ][ xᴰ , vert ]) →
         ⟨ fᴰ'' Cᴰ.⋆ᴰ π₁ , fᴰ'' Cᴰ.⋆ᴰ π₂ ⟩ ≡ fᴰ''
      η fᴰ'' = retIsEq (vbp .universalᴰ) fᴰ''
