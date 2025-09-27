module Cubical.Categories.Constructions.Free.CartesianCategory.Nf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Relation.Nullary

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver

private
  variable
    ℓq ℓq' : Level

module _ (Q : ×Quiver ℓq ℓq') where
  private
    module Q = ×QuiverNotation Q
  -- morally, we want normal and neutral terms to be a sort of profunctor on the
  -- syntactic category, but it seems difficult to do that directly, so we'll
  -- first manually define "Type-valued" "profunctors" and prove everything is a
  -- set after the fact
  module _ (Γ : Q.Ob) where
    data NormalForm : (τ : Q.Ob) → Type (ℓ-max ℓq ℓq')
    data NeutralTerm : (τ : Q.Ob) → Type (ℓ-max ℓq ℓq')

    data NeutralTerm where
      var : ∀{τ} → (τ Eq.≡ Γ) → NeutralTerm τ
      proj₁ : ∀{τ₁ τ₂} → NeutralTerm (τ₁ × τ₂) → NeutralTerm τ₁
      proj₂ : ∀{τ₁ τ₂} → NeutralTerm (τ₁ × τ₂) → NeutralTerm τ₂
      symb : ∀{τ} → (f : Q.Mor) → τ Eq.≡ Q.Cod f → NormalForm (Q.Dom f) → NeutralTerm τ

    data NormalForm where
      shift : ∀{x} → NeutralTerm (↑ x) → NormalForm (↑ x)
      pair : ∀{τ₁ τ₂} → NormalForm τ₁ → NormalForm τ₂ → NormalForm (τ₁ × τ₂)
      uniq : NormalForm ⊤

  module _ (Discrete-Ob : Discrete Q.Ob) (Discrete-Mor : Discrete Q.Mor) where
