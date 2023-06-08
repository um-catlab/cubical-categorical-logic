module Syntax.STLC.Semantics.Lindenbaum where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Data.FinSet
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Presheaf.Representable

open import Syntax.STLC renaming (Tm to Term; Ty to STy)
open import NaturalModels.Cartesian
open import NamedContext
open import UMP

open Functor

private
  variable ℓ ℓ' : Level

module _ {Σ₀ : Sig₀ ℓ}{Σ₁ : Sig₁ Σ₀ ℓ'} where
  open Category
  open SimplyTypedCategory

  STTCtx : Category _ _
  STTCtx .ob = Ctx (STy Σ₀)
  STTCtx .Hom[_,_] Δ Γ =
    substitution (Term Σ₁ Δ) Γ -- substitution (Term Σ₁ Δ) Γ
  STTCtx .id {Γ} = id-subst Γ
  STTCtx ._⋆_ {z = Γ} = λ δ γ → comp-subst {Γ = Γ} γ δ -- comp-subst γ δ
  STTCtx .⋆IdL {y = Γ} = comp-subst-IdInp {Γ = Γ}
  STTCtx .⋆IdR {y = Γ} = comp-subst-IdOutp {Γ = Γ}
  STTCtx .⋆Assoc {w = Γ} = λ f g h → comp-subst-Assoc {Γ = Γ} h g f
  STTCtx .isSetHom {y = Γ} = isSetTTProof.isSetSubst Σ₀ Σ₁ _ Γ

  Tm-presheaf : ∀ A → Presheaf STTCtx _
  Tm-presheaf A .F-ob Γ = (Term Σ₁ Γ A) , isSetTTProof.isSetTm Σ₀ Σ₁ Γ A
  Tm-presheaf A .F-hom = λ γ M → M ⟨ γ ⟩
  Tm-presheaf A .F-id = funExt subst-idInp
  Tm-presheaf A .F-seq γ δ = funExt λ M → subst-Assoc M γ δ

  open UnivElt
  open isUniversal
  Tm-univElt : ∀ A → UnivElt STTCtx (Tm-presheaf A)
  Tm-univElt A .vertex = singleton A
  Tm-univElt A .element = ivar tt
  Tm-univElt A .universal .coinduction M tt = M
  Tm-univElt A .universal .commutes M = refl
  Tm-univElt A .universal .is-uniq M M/var var*M/var≡M =
    funExt (λ x → var*M/var≡M)

  open Ctx
  open CartesianCategory
  open UnivElt
  open isUniversal

  -- the "Lindenbaum algebra" of terms/Syntactic category
  Lindenbaum : SimplyTypedCategory _ _ _ _
  Lindenbaum .B .cat = STTCtx
  Lindenbaum .B .finite-products J Γs .vertex = finProd J Γs
  Lindenbaum .B .finite-products J Γs .element j x = ivar (j , x)
  Lindenbaum .B .finite-products J Γs .universal .coinduction Ms (j , x) =
    Ms j x
  Lindenbaum .B .finite-products J Γs .universal .commutes ϕ = refl
  Lindenbaum .B .finite-products J Γs .universal .is-uniq ϕ f commutes =
    funExt (λ (j , x) → λ i → commutes i j x)
  Lindenbaum .Ty = (STy Σ₀)
  Lindenbaum .Tm = Tm-presheaf
  Lindenbaum .Tm-repr = Tm-univElt
