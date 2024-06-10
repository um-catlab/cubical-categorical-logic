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
  -- meant to be used as `module B = open VerticalBinProductsAtNotation vbp`
  module VerticalBinProductsAtNotation {cᴰ cᴰ' : Cᴰ.ob[ c ]}
    (vbp : VerticalBinProductsAt Cᴰ (cᴰ , cᴰ')) where

    vert-cᴰ×cᴰ' : Cᴰ.ob[ c ]
    vert-cᴰ×cᴰ' = vbp .vertexᴰ

    -- shorthand for terminal vertical cone
    vert-π₁₂ :
      Cᴰ.Hom[ C .id ][ vert-cᴰ×cᴰ' , cᴰ ] × Cᴰ.Hom[ C .id ][ vert-cᴰ×cᴰ' , cᴰ' ]
    vert-π₁₂ = vbp .elementᴰ
    vert-π₁ = vert-π₁₂ .fst
    vert-π₂ = vert-π₁₂ .snd

    module _ {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{f : C [ x , c ]} where
      vert-pair : Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ ] →
        Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ' ] →
        Cᴰ.Hom[ f ][ xᴰ , vert-cᴰ×cᴰ' ]
      vert-pair fᴰ fᴰ' = invIsEq (vbp .universalᴰ) (fᴰ , fᴰ')

      vert-pair' : Cᴰ.Hom[ f ][ xᴰ , cᴰ ] →
        Cᴰ.Hom[ f ][ xᴰ , cᴰ' ] →
        Cᴰ.Hom[ f ][ xᴰ , vert-cᴰ×cᴰ' ]
      vert-pair' fᴰ fᴰ' = vert-pair (fᴰ Cᴰ.⋆ᴰ Cᴰ.idᴰ) (fᴰ' Cᴰ.⋆ᴰ Cᴰ.idᴰ)

      vert-β : (fᴰ : Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ ]) →
        (fᴰ' : Cᴰ.Hom[ f ⋆⟨ C ⟩ C .id ][ xᴰ , cᴰ' ]) →
        (vert-pair fᴰ fᴰ' Cᴰ.⋆ᴰ vert-π₁ , vert-pair fᴰ fᴰ' Cᴰ.⋆ᴰ vert-π₂) ≡
        (fᴰ , fᴰ')
      vert-β fᴰ fᴰ' = secIsEq (vbp .universalᴰ) (fᴰ , fᴰ')

      vert-β' : (fᴰ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ]) →
        (fᴰ' : Cᴰ.Hom[ f ][ xᴰ , cᴰ' ]) →
        (vert-pair' fᴰ fᴰ' Cᴰ.⋆ᴰ vert-π₁ , vert-pair' fᴰ fᴰ' Cᴰ.⋆ᴰ vert-π₂) ≡
        (fᴰ Cᴰ.⋆ᴰ Cᴰ.idᴰ , fᴰ' Cᴰ.⋆ᴰ Cᴰ.idᴰ)
      vert-β' fᴰ fᴰ' = vert-β (fᴰ Cᴰ.⋆ᴰ Cᴰ.idᴰ)  (fᴰ' Cᴰ.⋆ᴰ Cᴰ.idᴰ)

      vert-η : (fᴰ'' : Cᴰ.Hom[ f ][ xᴰ , vert-cᴰ×cᴰ' ]) →
         vert-pair (fᴰ'' Cᴰ.⋆ᴰ vert-π₁) (fᴰ'' Cᴰ.⋆ᴰ vert-π₂) ≡ fᴰ''
      vert-η fᴰ'' = retIsEq (vbp .universalᴰ) fᴰ''

---- meant to be used as `module B = open VerticalBinProductsNotation vbps`
--module VerticalBinProductsNotation
--  {C  : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--  (vbps : VerticalBinProducts Cᴰ) where
--  private module Cᴰ = Categoryᴰ Cᴰ
--  module _ (c : C .ob)(cᴰ cᴰ' : Cᴰ.ob[ c ]) where
--    open VerticalBinProductsAtNotation (vbps (cᴰ , cᴰ')) public
--
--  vert-× = vert-cᴰ×cᴰ'
--  syntax vert-× c cᴰ c'ᴰ = cᴰ ×[ c ] c'ᴰ
