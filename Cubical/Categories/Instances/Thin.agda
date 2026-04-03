module Cubical.Categories.Instances.Thin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function


open import Cubical.Categories.Category

private
  variable ℓ ℓ' : Level

open Category

record Preorder ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    ob : Type ℓ
    _≤_ : ob → ob → Type ℓ'
    rfl : ∀ {a} → a ≤ a
    trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    isProp≤ : ∀ {a b} → isProp (a ≤ b)

module _ (P : Preorder ℓ ℓ') where
  private module P = Preorder P
  ThinCategory : Category ℓ ℓ'
  ThinCategory .ob = P.ob
  ThinCategory .Hom[_,_] = P._≤_
  ThinCategory .id = P.rfl
  ThinCategory ._⋆_ = P.trans
  ThinCategory .⋆IdL = λ f → P.isProp≤ _ _
  ThinCategory .⋆IdR = λ f → P.isProp≤ _ _
  ThinCategory .⋆Assoc = λ f g h → P.isProp≤ _ _
  ThinCategory .isSetHom = isProp→isSet $ P.isProp≤
