module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.AllocGetFresh where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Discrete
open import Cubical.Data.Fin
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl ; ≤-trans ; ≤-sucℕ)
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt

open Functor
open NatTrans
open PshHom

{- Reading the freshly allocated location returns its initial value.

  alloc b (λ i → get i (λ c → k i c))
    = alloc b (λ i → k i b)
-}
alloc-get-freshᵗ : ∀ {Γ A}
  (b : Γ ⊢ BoolVal)
  (k : (Γ V.× Ref) V.× BoolVal ⊢ T .F-ob A) →
  allocᵗ b (getᵗ V.π₂ k) ≡
  allocᵗ b ((V.id V.,p (V.π₁ V.⋆ b)) V.⋆ k)
alloc-get-freshᵗ {Γ = Γ} {A = A} b k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      q : n ≤ suc m
      q = ≤-trans n≤m ≤-sucℕ
      γ⁺ = Γ .F-hom q γ
      fresh : Fin (suc m)
      fresh = flast {k = m}
      bₙ = b .N-ob n γ
      b⁺ = b .N-ob (suc m) γ⁺
      τ = extendStore {n = m} bₙ σ
      fresh-id = funExt⁻ (Ref .F-id {x = suc m}) fresh
      b-nat = funExt⁻ (b .N-hom q) γ
      context-id = funExt⁻ ((Γ V.× Ref) .F-id) (γ⁺ , fresh)
      value-path =
        cong (λ r → lookupStore {n = suc m} r τ) fresh-id
        ∙ extendStore-fresh {n = m} bₙ σ
        ∙ sym b-nat
    in
    allocᵗ-run b (getᵗ V.π₂ k) n γ m n≤m σ
    ∙ cong (extendResult A ≤-sucℕ)
        (getᵗ-run {A = A} V.π₂ k (suc m) (γ⁺ , fresh)
          (suc m) ≤-refl τ)
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ δ → k .N-ob (suc m)
          (δ , lookupStore {n = suc m}
            (weakenRef {n = suc m} {m = suc m} ≤-refl fresh) τ)
          (suc m) ≤-refl τ) context-id)
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ v → k .N-ob (suc m) ((γ⁺ , fresh) , v)
          (suc m) ≤-refl τ) value-path)
    ∙ sym (allocᵗ-current-run b k n γ m n≤m σ))
