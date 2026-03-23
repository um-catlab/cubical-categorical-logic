module Cubical.Categories.FixedPoint where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

open Category
module _ {ℓ ℓ'} (C : Category ℓ ℓ') (𝟙 : C .ob) where
  private
    module C = Category C
  fixed-point : {x : C .ob} → C [ x , x ] → Type _
  fixed-point {x} f = Σ[ fix⟨f⟩ ∈ C [ 𝟙 , x ] ] (fix⟨f⟩ C.⋆ f) ≡ fix⟨f⟩

