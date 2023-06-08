module Syntax.STLC.Semantics.CTStructure.Lindenbaum where

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
open import NaturalModels.CTStructure
open import NamedContext
open import UMP

open Functor

private
  variable ℓ ℓ' : Level

module _ {Σ₀ : Sig₀ ℓ}{Σ₁ : Sig₁ Σ₀ ℓ'} where
  open Category
  open CTStructure

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

  open Ctx
  open CartesianCategory
  open UnivElt
  open isUniversal
  Lindenbaum : CTStructure _ _ _
  Lindenbaum .B .cat = STTCtx
  Lindenbaum .B .finite-products J Γs .vertex = finProd J Γs
  Lindenbaum .B .finite-products J Γs .element j x = ivar (j , x)
  Lindenbaum .B .finite-products J Γs .universal .coinduction Ms (j , x) =
    Ms j x
  Lindenbaum .B .finite-products J Γs .universal .commutes ϕ = refl
  Lindenbaum .B .finite-products J Γs .universal .is-uniq ϕ f commutes =
    funExt (λ (j , x) → λ i → commutes i j x)
  Lindenbaum .Ty = STy Σ₀
  Lindenbaum .sole = singleton
