{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.Renamings where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Base
  using (Expr; FreeCartesianClosedCategory)
open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Instances.Free.CartesianCategory.Base
open import Cubical.Categories.Instances.Free.CartesianCategory.UncurriedElim
open import Cubical.Categories.Instances.Free.CartesianCategory.Variables
  using (Type→×Quiver; normVar; normVar≡)

private
  variable ℓQ ℓQ' : Level

open Functor

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private
    module Q = ×⇒Quiver Q
    module FREECCC = CartesianClosedCategory (FreeCartesianClosedCategory Q)

  RenQuiver : ×Quiver ℓQ ℓ-zero
  RenQuiver = Type→×Quiver Q.obExpr

  REN : Category ℓQ ℓQ
  REN = |FreeCartesianCategory| RenQuiver

  Ctx : Type ℓQ
  Ctx = ×Quiver.Expr RenQuiver

  Ren : Ctx → Ctx → Type ℓQ
  Ren = Exp RenQuiver

  Var : Ctx → Q.obExpr → Type ℓQ
  Var Γ A = Ren Γ (↑ A)

  RenamingTerm : Functor REN FREECCC.C
  RenamingTerm = rec RenQuiver FREECCC.CC
    (mkInterpᴰ (λ A → A) λ ())

  contextType : Ctx → Q.obExpr
  contextType = RenamingTerm .F-ob

  renamingTerm : ∀ {Δ Γ} → Ren Δ Γ → Expr Q (contextType Δ) (contextType Γ)
  renamingTerm = RenamingTerm .F-hom

  Term : Ctx → Q.obExpr → Type (ℓ-max ℓQ ℓQ')
  Term Γ A = Expr Q (contextType Γ) A

  ren : ∀ {Δ Γ A} → Ren Δ Γ → Var Γ A → Var Δ A
  ren ρ v = normVar Q.obExpr _ (ρ ⋆ₑ v)

  ren≡ : ∀ {Δ Γ A} (ρ : Ren Δ Γ) (v : Var Γ A) → ren ρ v ≡ ρ ⋆ₑ v
  ren≡ ρ v = normVar≡ Q.obExpr _ (ρ ⋆ₑ v)

  renId : ∀ {Γ A} (v : Var Γ A) → ren idₑ v ≡ v
  renId v = ren≡ idₑ v ∙ ⋆ₑIdL v

  ren⋆ : ∀ {Θ Δ Γ A} (σ : Ren Θ Δ) (ρ : Ren Δ Γ) (v : Var Γ A)
    → ren σ (ren ρ v) ≡ ren (σ ⋆ₑ ρ) v
  ren⋆ σ ρ v = cong (normVar Q.obExpr _)
    (cong (σ ⋆ₑ_) (ren≡ ρ v) ∙ sym (⋆ₑAssoc σ ρ v))

  extendRenaming : ∀ {Δ Γ} A → Ren Δ Γ → Ren (Δ × (↑ A)) (Γ × (↑ A))
  extendRenaming A ρ = ⟨ π₁ ⋆ₑ ρ , π₂ ⟩

  extend-id : ∀ {Γ} A → extendRenaming {Γ} A idₑ ≡ idₑ
  extend-id A = cong₂ ⟨_,_⟩ (⋆ₑIdR π₁ ∙ sym (⋆ₑIdL π₁)) (sym (⋆ₑIdL π₂))
    ∙ sym ×η

  extend-seq : ∀ {Θ Δ Γ} A (σ : Ren Θ Δ) (ρ : Ren Δ Γ)
    → extendRenaming A σ ⋆ₑ extendRenaming A ρ ≡ extendRenaming A (σ ⋆ₑ ρ)
  extend-seq A σ ρ = ×η
    ∙ cong₂ ⟨_,_⟩
        (⋆ₑAssoc σ⁺ ρ⁺ π₁ ∙ cong (σ⁺ ⋆ₑ_) ×β₁ ∙ sym (⋆ₑAssoc σ⁺ π₁ ρ)
          ∙ cong (_⋆ₑ ρ) ×β₁ ∙ ⋆ₑAssoc π₁ σ ρ)
        (⋆ₑAssoc σ⁺ ρ⁺ π₂ ∙ cong (σ⁺ ⋆ₑ_) ×β₂ ∙ ×β₂)
    where
    σ⁺ = extendRenaming A σ
    ρ⁺ = extendRenaming A ρ

  wkRen : ∀ {Γ} A → Ren (Γ × (↑ A)) Γ
  wkRen A = π₁

  vz : ∀ {Γ A} → Var (Γ × (↑ A)) A
  vz = π₂

  weakening-natural : ∀ {Δ Γ} A (ρ : Ren Δ Γ)
    → extendRenaming A ρ ⋆ₑ wkRen A ≡ wkRen A ⋆ₑ ρ
  weakening-natural A ρ = ×β₁

  ren-extend-vz : ∀ {Δ Γ} A (ρ : Ren Δ Γ)
    → ren (extendRenaming A ρ) vz ≡ vz
  ren-extend-vz A ρ = refl

  vs : ∀ {Γ A B} → Var Γ A → Var (Γ × (↑ B)) A
  vs v = π₁ ⋆ₑ v
