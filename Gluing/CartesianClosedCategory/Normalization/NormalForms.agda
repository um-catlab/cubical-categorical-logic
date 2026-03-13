{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.Normalization.NormalForms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Cartesian.Base

import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver as PQ
open PQ using (×Quiver; module ×Quiver)
import Cubical.Categories.Instances.Free.CartesianCategory.Forded as FCC
import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded as FCCC
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver

open import Gluing.CartesianClosedCategory.Normalization.Renamings as Ren

private
  variable ℓQ ℓQ' : Level

open Category
open Functor

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private
    module Q = ×⇒Quiver Q
    ℓ = ℓ-max ℓQ ℓQ'

    -- Renamings infrastructure
    REN-×Q = Ren.REN-×Quiver Q
    |REN|' = Ren.|REN| Q
    ι' = Ren.ι Q
    ι-ob' = Ren.ι-ob Q
    |CCC| = Ren.|FREE-CCC| Q

  -- Context and type abbreviations
  -- Ctx = ProdExpr (CCCExpr Q.ob), uses PQ.↑_ and PQ._×_ constructors
  -- Ty = CCCExpr Q.ob, uses bare ↑_, _×_, ⊤, _⇒_ constructors
  Ctx : Type ℓQ
  Ctx = |REN|' .ob

  Ty : Type ℓQ
  Ty = Q.obExpr  -- CCCExpr Q.ob

  -- Renaming morphism abbreviation
  Ren' : Ctx → Ctx → Type ℓ
  Ren' = Ren.Ren Q

  -- CCC composition (local abbreviation)
  private
    infixl 15 _⋆CCC_
    _⋆CCC_ : ∀ {A B C : Ty}
      → |CCC| [ A , B ] → |CCC| [ B , C ] → |CCC| [ A , C ]
    _⋆CCC_ = |CCC| ._⋆_

    pair' : ∀ {Γ A B : Ty}
      → FCCC.Expr Q Γ A → FCCC.Expr Q Γ B → FCCC.Expr Q Γ (A × B)
    pair' = FCCC.⟨_,_⟩' Q

  -- Mutual inductive types for normal and neutral forms
  -- PQ.↑_ lifts a type to a singleton context
  -- PQ._×_ is the context product
  mutual
    data Nf (Γ : Ctx) : Ty → Type ℓ where
      lamNf  : ∀ {A B} → Nf (Γ PQ.× (PQ.↑ A)) B → Nf Γ (A ⇒ B)
      pairNf : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A × B)
      unitNf : Nf Γ ⊤
      neNf   : ∀ {a} → Ne Γ (↑ a) → Nf Γ (↑ a)

    data Ne (Γ : Ctx) : Ty → Type ℓ where
      varNe  : ∀ {A} → Ren' Γ ((PQ.↑ A)) → Ne Γ A
      appNe  : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
      fstNe  : ∀ {A B} → Ne Γ (A × B) → Ne Γ A
      sndNe  : ∀ {A B} → Ne Γ (A × B) → Ne Γ B
      genNe  : (e : Q.mor) → Nf Γ (Q.dom e) → Ne Γ (Q.cod e)

  -- Helper: extend a renaming by a fresh variable
  wkRen : ∀ {Δ Γ A} → Ren' Δ Γ
    → Ren' (Δ PQ.× (PQ.↑ A)) (Γ PQ.× (PQ.↑ A))
  wkRen σ = FCC.⟨_,_⟩' REN-×Q
    (FCC.π₁' REN-×Q ⋆⟨ |REN|' ⟩ σ)
    (FCC.π₂' REN-×Q)

  -- Renaming action (mutual recursion)
  mutual
    renNf : ∀ {Δ Γ A} → Ren' Δ Γ → Nf Γ A → Nf Δ A
    renNf σ (lamNf t)    = lamNf (renNf (wkRen σ) t)
    renNf σ (pairNf a b) = pairNf (renNf σ a) (renNf σ b)
    renNf σ unitNf       = unitNf
    renNf σ (neNf n)     = neNf (renNe σ n)

    renNe : ∀ {Δ Γ A} → Ren' Δ Γ → Ne Γ A → Ne Δ A
    renNe σ (varNe v)    = varNe (σ ⋆⟨ |REN|' ⟩ v)
    renNe σ (appNe n a)  = appNe (renNe σ n) (renNf σ a)
    renNe σ (fstNe n)    = fstNe (renNe σ n)
    renNe σ (sndNe n)    = sndNe (renNe σ n)
    renNe σ (genNe e nf) = genNe e (renNf σ nf)

  -- Embedding normal/neutral forms into CCC expressions
  mutual
    ⌈_⌉nf : ∀ {Γ A} → Nf Γ A → FCCC.Expr Q (ι-ob' Γ) A
    ⌈ lamNf t ⌉nf    = FCCC.lam' Q ⌈ t ⌉nf
    ⌈ pairNf a b ⌉nf = pair' ⌈ a ⌉nf ⌈ b ⌉nf
    ⌈ unitNf ⌉nf     = FCCC.!ₑ' Q
    ⌈ neNf n ⌉nf     = ⌈ n ⌉ne

    ⌈_⌉ne : ∀ {Γ A} → Ne Γ A → FCCC.Expr Q (ι-ob' Γ) A
    ⌈ varNe v ⌉ne    = ι' .F-hom v
    ⌈ appNe n a ⌉ne  = pair' ⌈ n ⌉ne ⌈ a ⌉nf ⋆CCC FCCC.eval' Q
    ⌈ fstNe n ⌉ne    = ⌈ n ⌉ne ⋆CCC FCCC.π₁' Q
    ⌈ sndNe n ⌉ne    = ⌈ n ⌉ne ⋆CCC FCCC.π₂' Q
    ⌈ genNe e nf ⌉ne = ⌈ nf ⌉nf ⋆CCC FCCC.↑ₑ Q e

  -- Renaming functoriality: identity
  private
    pairRen : ∀ {Δ A B} → Ren' Δ A → Ren' Δ B → Ren' Δ (A PQ.× B)
    pairRen = FCC.⟨_,_⟩' REN-×Q

    wkRen-id : ∀ {Γ A} → wkRen {A = A} (|REN|' .id {Γ}) ≡ |REN|' .id
    wkRen-id =
      cong (λ x → pairRen x (FCC.π₂' REN-×Q)) (|REN|' .⋆IdR _)
      ∙ sym (FCC.×η Eq.refl _
        ∙ cong₂ pairRen (|REN|' .⋆IdL _) (|REN|' .⋆IdL _))

  mutual
    renNf-id : ∀ {Γ A} (nf : Nf Γ A) → renNf (|REN|' .id) nf ≡ nf
    renNf-id (lamNf t) =
      cong lamNf (cong (λ σ → renNf σ t) wkRen-id ∙ renNf-id t)
    renNf-id (pairNf a b) = cong₂ pairNf (renNf-id a) (renNf-id b)
    renNf-id unitNf = refl
    renNf-id (neNf n) = cong neNf (renNe-id n)

    renNe-id : ∀ {Γ A} (ne : Ne Γ A) → renNe (|REN|' .id) ne ≡ ne
    renNe-id (varNe v) = cong varNe (|REN|' .⋆IdL v)
    renNe-id (appNe n a) = cong₂ appNe (renNe-id n) (renNf-id a)
    renNe-id (fstNe n) = cong fstNe (renNe-id n)
    renNe-id (sndNe n) = cong sndNe (renNe-id n)
    renNe-id (genNe e nf) = cong (genNe e) (renNf-id nf)

  -- Renaming functoriality: composition
  private
    wkRen-⋆ : ∀ {Θ Δ Γ A} (σ : Ren' Θ Δ) (τ : Ren' Δ Γ)
      → wkRen {A = A} (σ ⋆⟨ |REN|' ⟩ τ) ≡ wkRen σ ⋆⟨ |REN|' ⟩ wkRen τ
    wkRen-⋆ σ τ = sym (
      FCC.×η Eq.refl (wkRen σ ⋆⟨ |REN|' ⟩ wkRen τ)
      ∙ cong₂ pairRen
          (|REN|' .⋆Assoc _ _ _
            ∙ cong (λ x → wkRen σ ⋆⟨ |REN|' ⟩ x) FCC.×β₁
            ∙ sym (|REN|' .⋆Assoc _ _ _)
            ∙ cong (λ x → x ⋆⟨ |REN|' ⟩ τ) FCC.×β₁
            ∙ |REN|' .⋆Assoc _ _ _)
          (|REN|' .⋆Assoc _ _ _
            ∙ cong (λ x → wkRen σ ⋆⟨ |REN|' ⟩ x) FCC.×β₂
            ∙ FCC.×β₂))

  mutual
    renNf-⋆ : ∀ {Θ Δ Γ A} (σ : Ren' Θ Δ) (τ : Ren' Δ Γ) (nf : Nf Γ A)
      → renNf (σ ⋆⟨ |REN|' ⟩ τ) nf ≡ renNf σ (renNf τ nf)
    renNf-⋆ σ τ (lamNf t) =
      cong lamNf (cong (λ ρ → renNf ρ t) (wkRen-⋆ σ τ) ∙ renNf-⋆ (wkRen σ) (wkRen τ) t)
    renNf-⋆ σ τ (pairNf a b) = cong₂ pairNf (renNf-⋆ σ τ a) (renNf-⋆ σ τ b)
    renNf-⋆ σ τ unitNf = refl
    renNf-⋆ σ τ (neNf n) = cong neNf (renNe-⋆ σ τ n)

    renNe-⋆ : ∀ {Θ Δ Γ A} (σ : Ren' Θ Δ) (τ : Ren' Δ Γ) (ne : Ne Γ A)
      → renNe (σ ⋆⟨ |REN|' ⟩ τ) ne ≡ renNe σ (renNe τ ne)
    renNe-⋆ σ τ (varNe v) = cong varNe (|REN|' .⋆Assoc σ τ v)
    renNe-⋆ σ τ (appNe n a) = cong₂ appNe (renNe-⋆ σ τ n) (renNf-⋆ σ τ a)
    renNe-⋆ σ τ (fstNe n) = cong fstNe (renNe-⋆ σ τ n)
    renNe-⋆ σ τ (sndNe n) = cong sndNe (renNe-⋆ σ τ n)
    renNe-⋆ σ τ (genNe e nf) = cong (genNe e) (renNf-⋆ σ τ nf)
