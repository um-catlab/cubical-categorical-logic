module Cubical.Categories.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base

private
  variable
    ℓ ℓ' : Level

module Reasoning (C : Category ℓ ℓ') where
  open Category C
  ⟨⟩⋆⟨_⟩ : ∀ {x y z} {f : C [ x , y ]} {g g' : C [ y , z ]}
          → g ≡ g' → f ⋆ g ≡ f ⋆ g'
  ⟨⟩⋆⟨ ≡g ⟩ = cong (_ ⋆_) ≡g

  ⟨_⟩⋆⟨⟩ : ∀ {x y z} {f f' : C [ x , y ]} {g : C [ y , z ]}
          → f ≡ f' → f ⋆ g ≡ f' ⋆ g
  ⟨ ≡f ⟩⋆⟨⟩ = cong (_⋆ _) ≡f

