module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.AllocSetOld where

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

{- Allocation commutes with writing an already existing location j.

  alloc b (λ i → set j c (k i))
    = set j c (alloc b (λ i → k i))
-}
alloc-set-oldᵗ : ∀ {Γ A}
  (j : Γ ⊢ Ref) (b c : Γ ⊢ BoolVal)
  (k : Γ V.× Ref ⊢ T .F-ob A) →
  allocᵗ b (setᵗ (V.π₁ V.⋆ j) (V.π₁ V.⋆ c) k) ≡
  setᵗ j c (allocᵗ b k)
alloc-set-oldᵗ {Γ = Γ} {A = A} j b c k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      q : n ≤ suc m
      q = ≤-trans n≤m ≤-sucℕ
      γ⁺ : Γ .F-ob (suc m) .fst
      γ⁺ = Γ .F-hom q γ
      fresh : Fin (suc m)
      fresh = flast {k = m}
      wj : Fin m
      wj = weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)
      old : Fin (suc m)
      old = weakenRef {n = m} {m = suc m} ≤-sucℕ wj
      j⁺ : Fin (suc m)
      j⁺ = j .N-ob (suc m) γ⁺
      rj : Fin (suc m)
      rj = weakenRef {n = suc m} {m = suc m} ≤-refl j⁺
      cₙ : Bool
      cₙ = c .N-ob n γ
      c⁺ : Bool
      c⁺ = c .N-ob (suc m) γ⁺
      σc : Fin m → Bool
      σc = updateStore {n = m} wj cₙ σ
      rj≡old =
        funExt⁻ (Ref .F-id {x = suc m}) j⁺
        ∙ funExt⁻ (j .N-hom q) γ
        ∙ sym (weakenRef-comp n≤m ≤-sucℕ (j .N-ob n γ))
      c⁺≡cₙ = funExt⁻ (c .N-hom q) γ
      store-path =
        cong₂
          (λ r v → updateStore {n = suc m} r v
            (extendStore {n = m} (b .N-ob n γ) σ))
          rj≡old c⁺≡cₙ
        ∙ alloc-set-distinct {n = m} wj (b .N-ob n γ) cₙ σ
    in
    allocᵗ-run {A = A} b
      (setᵗ (V.π₁ V.⋆ j) (V.π₁ V.⋆ c) k)
      n γ m n≤m σ
    ∙ cong (extendResult A ≤-sucℕ)
        (setᵗ-run {A = A} (V.π₁ V.⋆ j) (V.π₁ V.⋆ c) k
          (suc m) (γ⁺ , fresh) (suc m) ≤-refl
          (extendStore {n = m} (b .N-ob n γ) σ))
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ τ → k .N-ob (suc m) (γ⁺ , fresh)
          (suc m) ≤-refl τ) store-path)
    ∙ sym (allocᵗ-run {A = A} b k n γ m n≤m σc)
    ∙ sym (setᵗ-run {A = A} j c (allocᵗ b k) n γ m n≤m σ))
