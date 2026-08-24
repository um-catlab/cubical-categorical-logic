module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.GetSetCurrent where

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

{- Reading a location and writing its current value has no effect.

  get i (λ b → set i b t) = t
-}
opaque
  -- Naming this CCC composite is a type-checking boundary.  Expanding it in
  -- Downstream runner endpoints otherwise normalize the full product/lambda
  -- term during conversion.
  set-current-contᵗ : ∀ {Γ A} →
    (i : Γ ⊢ Ref) (t : Γ ⊢ T .F-ob A) →
    Γ V.× BoolVal ⊢ T .F-ob A
  set-current-contᵗ i t =
    setᵗ (V.π₁ V.⋆ i) V.π₂ (V.π₁ V.⋆ t)

  set-current-contᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (t : Γ ⊢ T .F-ob A)
    n (γ : (Γ V.× BoolVal) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → Bool) →
    set-current-contᵗ i t .N-ob n γ m n≤m σ ≡
    t .N-ob n (γ .fst) m n≤m
      (updateStore {n = m}
        (weakenRef {n = n} {m = m} n≤m (i .N-ob n (γ .fst)))
        (γ .snd) σ)
  set-current-contᵗ-run {A = A} i t n γ m n≤m σ =
    setᵗ-run {A = A} (V.π₁ V.⋆ i) V.π₂ (V.π₁ V.⋆ t)
      n γ m n≤m σ

opaque
  get-set-current-store : ∀ {Γ n m}
    (i : Γ ⊢ Ref) (γ : Γ .F-ob n .fst)
    (n≤m : n ≤ m) (σ : Fin m → Bool) →
    updateStore {n = m}
      (weakenRef {n = m} {m = m} ≤-refl
        (i .N-ob m (Γ .F-hom n≤m γ)))
      (lookupStore {n = m}
        (weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)) σ)
      σ ≡ σ
  get-set-current-store {Γ = Γ} {n = n} {m = m} i γ n≤m σ =
    let
      iₘ = i .N-ob m (Γ .F-hom n≤m γ)
      wi = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
      write≡wi =
        funExt⁻ (Ref .F-id {x = m}) iₘ
        ∙ funExt⁻ (i .N-hom n≤m) γ
    in
    cong (λ r → updateStore {n = m} r
      (lookupStore {n = m} wi σ) σ) write≡wi
    ∙ update-current {n = m} wi σ

opaque
  get-set-current-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (t : Γ ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → Bool) →
    getᵗ i (set-current-contᵗ i t) .N-ob n γ m n≤m σ ≡
    t .N-ob n γ m n≤m σ
  get-set-current-run {Γ = Γ} {A = A} i t n γ m n≤m σ =
    let
      γₘ = Γ .F-hom n≤m γ
      wi = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
    in
    getᵗ-run {Γ = Γ} {A = A} i (set-current-contᵗ i t)
      n γ m n≤m σ
    ∙ set-current-contᵗ-run i t m
        (γₘ , lookupStore {n = m} wi σ) m ≤-refl σ
    ∙ cong (λ τ → t .N-ob m γₘ m ≤-refl τ)
        (get-set-current-store i γ n≤m σ)
    ∙ cong (λ u → u m ≤-refl σ)
        (funExt⁻ (t .N-hom n≤m) γ)
    ∙ cong (λ q → t .N-ob n γ m q σ) (isProp≤ _ _)

get-set-currentᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (t : Γ ⊢ T .F-ob A) →
  getᵗ i (set-current-contᵗ i t) ≡ t
get-set-currentᵗ {A = A} i t =
  makeNatTransPath (funExt λ n → funExt λ γ →
    T-ext {A = A} (get-set-current-run i t n γ))
