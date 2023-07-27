{-# OPTIONS --safe #-}
module Cubical.Categories.CartesianCategory.BinaryCartesianCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open Category

private variable ℓ ℓ' : Level
record BinaryCartesianCategory ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cat : Category ℓ ℓ'
    prod : BinProducts cat
    ⊤ : cat .ob
    ! : ∀{A} → cat [ A , ⊤ ]
    ⊤η : ∀{A}{f : cat [ A , ⊤ ] } → f ≡ !
open BinaryCartesianCategory

-- nice syntax for specifying which category the product is in
module _ (𝓒 : BinaryCartesianCategory ℓ ℓ') where
  open Cubical.Categories.Limits.BinProduct.More.Notation (𝓒 .cat) (𝓒 .prod)
  pair-objects : _ → _ → _ -- agda constraint solver needs this signature
  pair-objects A B = A × B
  syntax pair-objects 𝓒 A B = A ×⟨ 𝓒 ⟩ B

-- define (strict) product preserving functors from 𝓒 to 𝓓
private variable ℓc ℓc' ℓd ℓd' : Level
module _ (𝓒 : BinaryCartesianCategory ℓc ℓc')(𝓓 : BinaryCartesianCategory ℓd ℓd') where
  open import Cubical.Categories.Functor
  record StrictCartesianFunctor : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓd ℓd')) where
    field
      functor : Functor (𝓒 .cat) (𝓓 .cat)
      preserves-× : ∀{A B} → functor ⟅ A ×⟨ 𝓒 ⟩ B ⟆ ≡ functor ⟅ A ⟆ ×⟨ 𝓓 ⟩ functor ⟅ B ⟆
      preserves-⊤ : functor ⟅ 𝓒 .⊤ ⟆ ≡ 𝓓 .⊤
