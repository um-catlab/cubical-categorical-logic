module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.GetGetCommute where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Discrete
open import Cubical.Data.Fin
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl ; isProp≤)
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt

open Functor
open NatTrans
open PshHom

{- Reads commute. No distinctness assumption is required.

  get i (λ b → get j (λ c → k b c))
    = get j (λ c → get i (λ b → k b c))
-}
opaque
  -- Keep the lifted inner read out of the exported equality endpoint's
  -- conversion problem.
  left-read-contᵗ : ∀ {Γ A} →
    (j : Γ ⊢ Ref)
    (k : (Γ V.× BoolVal) V.× BoolVal ⊢ T .F-ob A) →
    Γ V.× BoolVal ⊢ T .F-ob A
  left-read-contᵗ {Γ = Γ} j k =
    getᵗ (V.π₁ {a = Γ} {b = BoolVal} V.⋆ j) k

  left-read-contᵗ-run : ∀ {Γ A}
    (j : Γ ⊢ Ref)
    (k : (Γ V.× BoolVal) V.× BoolVal ⊢ T .F-ob A)
    n (δ : (Γ V.× BoolVal) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → Bool) →
    left-read-contᵗ j k .N-ob n δ m n≤m σ ≡
    k .N-ob m
      ((Γ V.× BoolVal) .F-hom n≤m δ ,
       lookupStore {n = m}
         (weakenRef {n = n} {m = m} n≤m
           ((V.π₁ {a = Γ} {b = BoolVal} V.⋆ j) .N-ob n δ)) σ)
      m ≤-refl σ
  left-read-contᵗ-run {Γ = Γ} {A = A} j k n δ m n≤m σ =
    getᵗ-run {Γ = Γ V.× BoolVal} {A = A}
      (V.π₁ {a = Γ} {b = BoolVal} V.⋆ j) k n δ m n≤m σ

opaque
  right-read-contᵗ : ∀ {Γ A} →
    (i : Γ ⊢ Ref)
    (k : (Γ V.× BoolVal) V.× BoolVal ⊢ T .F-ob A) →
    Γ V.× BoolVal ⊢ T .F-ob A
  right-read-contᵗ {Γ = Γ} i k =
    getᵗ (V.π₁ {a = Γ} {b = BoolVal} V.⋆ i) (swapLast V.⋆ k)

  right-read-contᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref)
    (k : (Γ V.× BoolVal) V.× BoolVal ⊢ T .F-ob A)
    n (δ : (Γ V.× BoolVal) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → Bool) →
    right-read-contᵗ i k .N-ob n δ m n≤m σ ≡
    (swapLast V.⋆ k) .N-ob m
      ((Γ V.× BoolVal) .F-hom n≤m δ ,
       lookupStore {n = m}
         (weakenRef {n = n} {m = m} n≤m
           ((V.π₁ {a = Γ} {b = BoolVal} V.⋆ i) .N-ob n δ)) σ)
      m ≤-refl σ
  right-read-contᵗ-run {Γ = Γ} {A = A} i k n δ m n≤m σ =
    getᵗ-run {Γ = Γ V.× BoolVal} {A = A}
      (V.π₁ {a = Γ} {b = BoolVal} V.⋆ i) (swapLast V.⋆ k)
      n δ m n≤m σ

get-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref)
  (k : (Γ V.× BoolVal) V.× BoolVal ⊢ T .F-ob A) →
  getᵗ i (left-read-contᵗ j k) ≡
  getᵗ j (right-read-contᵗ i k)
get-get-commuteᵗ {Γ = Γ} {A = A} i j k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      γₘ : Γ .F-ob m .fst
      γₘ = Γ .F-hom n≤m γ
      wi : Fin m
      wi = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
      wj : Fin m
      wj = weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)
      vi : Bool
      vi = lookupStore {n = m} wi σ
      vj : Bool
      vj = lookupStore {n = m} wj σ
      iₘ : Fin m
      iₘ = i .N-ob m γₘ
      jₘ : Fin m
      jₘ = j .N-ob m γₘ
      ri : Fin m
      ri = weakenRef {n = m} {m = m} ≤-refl iₘ
      rj : Fin m
      rj = weakenRef {n = m} {m = m} ≤-refl jₘ
      context-i-id = funExt⁻ ((Γ V.× BoolVal) .F-id) (γₘ , vi)
      γ-id = funExt⁻ (Γ .F-id) γₘ
      ri≡wi = funExt⁻ (Ref .F-id {x = m}) iₘ ∙ funExt⁻ (i .N-hom n≤m) γ
      rj≡wj = funExt⁻ (Ref .F-id {x = m}) jₘ ∙ funExt⁻ (j .N-hom n≤m) γ
    in
    getᵗ-run {A = A} i (left-read-contᵗ j k) n γ m n≤m σ
    ∙ left-read-contᵗ-run {Γ = Γ} {A = A} j k
        m (γₘ , vi) m ≤-refl σ
    ∙ cong (λ δ → k .N-ob m
        (δ , lookupStore {n = m} rj σ) m ≤-refl σ) context-i-id
    ∙ cong (λ c → k .N-ob m ((γₘ , vi) , c) m ≤-refl σ)
        (cong σ rj≡wj)
    ∙ sym (cong (λ b → k .N-ob m ((γₘ , b) , vj) m ≤-refl σ)
        (cong σ ri≡wi))
    ∙ sym (cong (λ δ → k .N-ob m
        ((δ , lookupStore {n = m} ri σ) , vj) m ≤-refl σ) γ-id)
    ∙ sym (right-read-contᵗ-run {Γ = Γ} {A = A} i k
        m (γₘ , vj) m ≤-refl σ)
    ∙ sym (getᵗ-run {A = A} j (right-read-contᵗ i k)
        n γ m n≤m σ))
