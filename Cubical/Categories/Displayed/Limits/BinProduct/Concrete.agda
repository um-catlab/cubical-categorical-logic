{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.BinProduct.Concrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Fibration.Base
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open UniversalElementᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  record VerticalBinProduct {x} (x₁ᴰ x₂ᴰ : Cᴰ.ob[ x ]) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')) where
    field
      prodᴰ : Cᴰ.ob[ x ]
      π₁ᴰ : Cᴰ.Hom[ C .id ][ prodᴰ , x₁ᴰ ]
      π₂ᴰ : Cᴰ.Hom[ C .id ][ prodᴰ , x₂ᴰ ]
      _,pᴰ_ : ∀ {y}{yᴰ}{f : C [ y , x ]}
        → (f₁ᴰ : Cᴰ.Hom[ f ][ yᴰ , x₁ᴰ ])
        → (f₂ᴰ : Cᴰ.Hom[ f ][ yᴰ , x₂ᴰ ])
        → Cᴰ.Hom[ f ][ yᴰ , prodᴰ ]
      β₁ᴰ : ∀ {y}{yᴰ}{f : C [ y , x ]}
        → (f₁ᴰ : Cᴰ.Hom[ f ][ yᴰ , x₁ᴰ ])
        → (f₂ᴰ : Cᴰ.Hom[ f ][ yᴰ , x₂ᴰ ])
        → ((f₁ᴰ ,pᴰ f₂ᴰ) Cᴰ.⋆ᴰ π₁ᴰ) Cᴰ.≡[ C .⋆IdR f ] f₁ᴰ
      β₂ᴰ : ∀ {y}{yᴰ}{f : C [ y , x ]}
        → (f₁ᴰ : Cᴰ.Hom[ f ][ yᴰ , x₁ᴰ ])
        → (f₂ᴰ : Cᴰ.Hom[ f ][ yᴰ , x₂ᴰ ])
        → ((f₁ᴰ ,pᴰ f₂ᴰ) Cᴰ.⋆ᴰ π₂ᴰ) Cᴰ.≡[ C .⋆IdR f ] f₂ᴰ
      ηᴰ : ∀ {y}{yᴰ}{f : C [ y , x ]}
        → (fᴰ : Cᴰ.Hom[ f ][ yᴰ , prodᴰ ])
        → fᴰ Cᴰ.≡[ sym (C .⋆IdR f) ] ((fᴰ Cᴰ.⋆ᴰ π₁ᴰ) ,pᴰ (fᴰ Cᴰ.⋆ᴰ π₂ᴰ))

  VerticalBinProducts : Type _
  VerticalBinProducts = ∀ x x₁ᴰ x₂ᴰ → VerticalBinProduct {x} x₁ᴰ x₂ᴰ
  open VerticalBinProduct
