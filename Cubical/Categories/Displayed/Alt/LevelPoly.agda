{-
  Displayed categories with dependent universe levels.

  We're limited by Agda universe levels
-}
module Cubical.Categories.Displayed.Alt.LevelPoly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Indiscrete

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

open Category
record Categoryᴰ (C : Category ℓC ℓC')
  (ℓCᴰ : C .ob → Level)
  (ℓCᴰ' : C .ob → C .ob → Level)
  : Typeω where
  no-eta-equality
  field
    ob[_] : (x : C .ob) → Type (ℓCᴰ x)
    Hom[_][_,_] : {x y : C .ob}
      → C [ x , y ] → ob[ x ] → ob[ y ]
      → Type (ℓCᴰ' x y)
    idᴰ : ∀ {x} {p : ob[ x ]} → Hom[ C .id ][ p , p ]
    _⋆ᴰ_ : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f ⋆⟨ C ⟩ g ][ xᴰ , zᴰ ]

  infixr 9 _⋆ᴰ_
  infixr 9 _∘ᴰ_

  _≡[_]_ : ∀ {x y xᴰ yᴰ} {f g : C [ x , y ]}
    → Hom[ f ][ xᴰ , yᴰ ] → f ≡ g → Hom[ g ][ xᴰ , yᴰ ] → Type (ℓCᴰ' x y)
  _≡[_]_ {x} {y} {xᴰ} {yᴰ} fᴰ p gᴰ = PathP (λ i → Hom[ p i ][ xᴰ , yᴰ ]) fᴰ gᴰ

  infix 2 _≡[_]_

  field
    ⋆IdLᴰ : ∀ {x y} {f : C [ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
      → idᴰ ⋆ᴰ fᴰ ≡[ C .⋆IdL f ] fᴰ
    ⋆IdRᴰ : ∀ {x y} {f : C [ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
      → fᴰ ⋆ᴰ idᴰ ≡[ C .⋆IdR f ] fᴰ
    ⋆Assocᴰ : ∀ {x y z w} {f : C [ x , y ]} {g : C [ y , z ]}  {h : C [ z , w ]}
      {xᴰ yᴰ zᴰ wᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ yᴰ , zᴰ ])
      (hᴰ : Hom[ h ][ zᴰ , wᴰ ])
      → (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ ≡[ C .⋆Assoc f g h ] fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ)
    isSetHomᴰ : ∀ {x y} {f : C [ x , y ]} {xᴰ yᴰ} → isSet Hom[ f ][ xᴰ , yᴰ ]

  -- composition: alternative to diagramatic order
  _∘ᴰ_ : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f ][ xᴰ , yᴰ ] → Hom[ f ⋆⟨ C ⟩ g ][ xᴰ , zᴰ ]
  g ∘ᴰ f = f ⋆ᴰ g


LEVEL : Category ℓ-zero ℓ-zero
LEVEL = Indiscrete Level
open Categoryᴰ

SET : Categoryᴰ LEVEL ℓ-suc ℓ-max
SET .ob[_] ℓ = hSet ℓ
SET .Hom[_][_,_] _ X Y = ⟨ X ⟩ → ⟨ Y ⟩
SET .idᴰ = λ z → z
SET ._⋆ᴰ_ = λ z z₁ z₂ → z₁ (z z₂)
SET .⋆IdLᴰ _ = refl
SET .⋆IdRᴰ _ = refl
SET .⋆Assocᴰ _ _ _ = refl
SET .isSetHomᴰ {yᴰ = Y} = isSet→ (Y .snd)
