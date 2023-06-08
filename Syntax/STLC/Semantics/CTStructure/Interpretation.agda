module Syntax.STLC.Semantics.CTStructure.Interpretation where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Syntax.STLC hiding (Tm) renaming (Ty to SimpleTy)
open import NaturalModels.CTStructure
open import NamedContext
open import UMP

private
  variable
    ℓ ℓ' ℓb ℓb' ℓt ℓt' : Level

open import Cubical.Categories.Presheaf.Representable
open CartesianCategory
open Category
open UnivElt
open Ctx
open Sig₁
open CTStructure

Interp₀ : Sig₀ ℓ → CTStructure ℓb ℓb' ℓt → Type _
Interp₀ Σ₀ C = Σ₀ .fst → C .Ty

interpTy : ∀ {Σ₀ : Sig₀ ℓ}{S : CTStructure ℓb ℓb' ℓt} →
           Interp₀ Σ₀ S → SimpleTy Σ₀ → S .Ty
interpTy i = i

interpCtx : ∀ {Σ₀ : Sig₀ ℓ}{S : CTStructure ℓb ℓb' ℓt} →
            Interp₀ Σ₀ S → Ctx (SimpleTy Σ₀) → S .B .cat .ob
interpCtx {S = S} i Γ =
  prod-ob (S .B) (varFinSet Γ) (λ x → sole S (i (Γ .el x)))

Interp₁ : ∀ {Σ₀ : Sig₀ ℓ}{S : CTStructure ℓb ℓb' ℓt} →
          Interp₀ Σ₀ S → Sig₁ Σ₀ ℓ' → Type _
Interp₁ {Σ₀ = Σ₀}{S = S} i Σ₁ =
  ∀ (f : Σ₁ .fun-symbol)
  → S .B .cat [ interpCtx {Σ₀ = Σ₀}{S = S} i (Σ₁ .src f) ,
                S .sole (interpTy {Σ₀ = Σ₀}{S = S} i (Σ₁ .tgt f)) ]
