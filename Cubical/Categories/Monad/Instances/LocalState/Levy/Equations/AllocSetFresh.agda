module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.AllocSetFresh where

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

-- Block interaction laws
------------------------------------------------------------------------

{- Writing the freshly allocated location replaces its initial value.

  alloc b (λ i → set i c (k i))
    = alloc c (λ i → k i)
-}
alloc-set-freshᵗ : ∀ {Γ A}
  (b c : Γ ⊢ BoolVal) (k : Γ V.× Ref ⊢ T .F-ob A) →
  allocᵗ b (setᵗ V.π₂ (V.π₁ V.⋆ c) k) ≡ allocᵗ c k
alloc-set-freshᵗ {Γ = Γ} {A = A} b c k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      q : n ≤ suc m
      q = ≤-trans n≤m ≤-sucℕ
      γ⁺ = Γ .F-hom q γ
      fresh : Fin (suc m)
      fresh = flast {k = m}
      c⁺ = c .N-ob (suc m) γ⁺
      cₙ = c .N-ob n γ
      fresh-id = funExt⁻ (Ref .F-id {x = suc m}) fresh
      c-nat = funExt⁻ (c .N-hom q) γ
      store-path =
        cong (λ r → updateStore {n = suc m} r c⁺
          (extendStore {n = m} (b .N-ob n γ) σ)) fresh-id
        ∙ update-fresh {n = m} (b .N-ob n γ) c⁺ σ
        ∙ cong (λ v → extendStore {n = m} v σ) c-nat
    in
    allocᵗ-run b (setᵗ V.π₂ (V.π₁ V.⋆ c) k)
      n γ m n≤m σ
    ∙ cong (extendResult A ≤-sucℕ)
        (setᵗ-run {A = A} V.π₂ (V.π₁ V.⋆ c) k
          (suc m) (γ⁺ , fresh) (suc m) ≤-refl
          (extendStore {n = m} (b .N-ob n γ) σ))
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ τ → k .N-ob (suc m) (γ⁺ , fresh)
          (suc m) ≤-refl τ) store-path)
    ∙ sym (allocᵗ-run c k n γ m n≤m σ))
