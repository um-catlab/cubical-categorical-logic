{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.Terminal.Concrete where

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
  record VerticalTerminal (x : C .ob) : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')) where
    field
      ⊤ᴰ : Cᴰ.ob[ x ]
      corecᴰ : ∀ {y yᴰ}{f : C [ y , x ]} → Cᴰ.Hom[ f ][ yᴰ , ⊤ᴰ ]
      ηᴰ : ∀  {y yᴰ}{f : C [ y , x ]} → (fᴰ : Cᴰ.Hom[ f ][ yᴰ , ⊤ᴰ ])
        → fᴰ ≡ corecᴰ

  VerticalTerminals = ∀ x → VerticalTerminal x
  
