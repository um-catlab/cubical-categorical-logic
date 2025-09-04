module Gluing.CartesianNormalization where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category

open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Constructions.Free.CartesianCategory.Base hiding (rec)
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver hiding (_×_)

private
  variable
    ℓq ℓq' : Level

module _ (Q : ×Quiver' ℓq ℓq') where
  private module Q = ×Quiver'Notation Q
  module _ (isGroupoidQ : isGroupoid Q.Ob) where
    Cl : CartesianCategory _ _
    Cl = FreeCartesianCategory (×Quiver'→×Quiver Q)
    open Category
    open CartesianCategory
    open BinProductsNotation (Cl .bp)
    open ProductQuiver
    open TerminalNotation (Cl .term)
    -- write normal forms by hand
    data NormalForm : (τ : Cl .C .ob) → (Γ : Cl .C .ob) → Type (ℓ-max ℓq ℓq')
    data NeutralTerm : (τ : Cl .C .ob) → (Γ : Cl .C .ob) → Type (ℓ-max ℓq ℓq')
    data NeutralTerm where
      var : ∀{τ : Cl .C .ob} → NeutralTerm τ τ
      proj₁ : ∀{τ₁ τ₂ Γ} → NeutralTerm (τ₁ × τ₂) Γ → NeutralTerm τ₁ Γ
      proj₂ : ∀{τ₁ τ₂ Γ} → NeutralTerm (τ₁ × τ₂) Γ → NeutralTerm τ₂ Γ
      symb : ∀(f : Q.mor){Γ}(M : NormalForm (Q.dom f) Γ) → NeutralTerm (↑ (Q.cod f)) Γ
      isSetNe : ∀{τ Γ} → isSet (NeutralTerm τ Γ)
    data NormalForm where
      shift : ∀{τ : Q.ob} {Γ} → NeutralTerm (↑ τ) Γ → NormalForm (↑ τ) Γ
      pair : ∀{τ₁ τ₂ Γ} → NormalForm τ₁ Γ → NormalForm τ₂ Γ → NormalForm (τ₁ × τ₂) Γ
      uniq : ∀{Γ} → NormalForm 𝟙 Γ
      isSetNf : ∀{τ Γ} → isSet (NormalForm τ Γ)
