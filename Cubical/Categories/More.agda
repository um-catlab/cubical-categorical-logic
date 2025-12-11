module Cubical.Categories.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Isomorphism

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

  private
    variable x y z w :  ob
  -- Syntax for chains of composition of morphisms
  -- annotated by their intermediate endpoints a la equational reasoning
  -- from Cubical.Foundations.Prelude
  step-→ : (x : ob) → C [ y , z ] → C [ x , y ] → C [ x , z ]
  step-→ _ g f = f ⋆ g

  infixr 2 step-→
  syntax step-→ x g f = x →⟨ f ⟩→ g


  →⟨⟩⟨⟩-syntax : (x y : ob) → C [ x , y ] → C [ y , z ] → C [ z , w ] → C [ x , w ]
  →⟨⟩⟨⟩-syntax x y f g h = f ⋆ (g ⋆ h)
  -- How much will this choice of association matter?

  infixr 3 →⟨⟩⟨⟩-syntax
  syntax →⟨⟩⟨⟩-syntax x y f g = x →⟨ f ⟩→ y →⟨ g ⟩→

  -- Deliberately not using a terminator in the same way that
  -- equational reasoning does
  --    _∎ : (x : A) → x ≡ x
  --    _ ∎ = refl
  -- because it would introduce a composition with the identity
  →⟨⟩∎-syntax : (x y : ob) → C [ x , y ] → C [ x , y ]
  →⟨⟩∎-syntax _ _ f = f

  infixr 2 →⟨⟩∎-syntax
  syntax →⟨⟩∎-syntax x y f = x →⟨ f ⟩∎ y

  private
    module _ {x y z w u v s}
      {f : C [ x , y ]} {g : C [ y , z ]} {h : C [ z , w ]}
      {k : C [ w , u ]} {l : C [ u , v ]} {m : C [ v , s ]} where

      test : C [ x , s ]
      test = x →⟨ f ⟩→ y →⟨ g ⟩→ z →⟨ h ⟩→ w →⟨ k ⟩→ u →⟨ l ⟩→ v →⟨ m ⟩∎ s

module CategoryNotation (C : Category ℓ ℓ') where
  ISOC = ISO C
  module ISOC = Reasoning ISOC
  open Reasoning C public
