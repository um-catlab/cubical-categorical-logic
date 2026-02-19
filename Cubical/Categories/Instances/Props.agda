{- TODO: -}
module Cubical.Categories.Instances.Props where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure


open import Cubical.Categories.Category
open import Cubical.Categories.HLevels
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Thin
open import Cubical.Categories.Instances.Sets

private
  variable ℓ : Level

open Functor

PROP : ∀ ℓ → Category (ℓ-suc ℓ) ℓ
PROP ℓ = ThinCategory (hProp ℓ) (λ P Q → ⟨ P ⟩ → ⟨ Q ⟩)
  (λ {a} z → z)
  (λ {a} {b} {c} z z₁ z₂ → z₁ (z z₂))
  λ {b = Q} → isProp→ (Q .snd)

hasPropHomsPROP : hasPropHoms (PROP ℓ)
hasPropHomsPROP {y = Q} = isProp→ (Q .snd)

PROP→SET : Functor (PROP ℓ) (SET ℓ)
PROP→SET .F-ob P = ⟨ P ⟩ , (isProp→isSet (P .snd))
PROP→SET .F-hom = λ z → z
PROP→SET .F-id = refl
PROP→SET .F-seq = λ _ _ → refl
