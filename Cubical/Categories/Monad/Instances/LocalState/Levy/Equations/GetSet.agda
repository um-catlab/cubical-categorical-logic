open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Nat.Order using (≤-refl)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet)
open import Cubical.Functions.FunExtEquiv using (funExt₃)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.GetSet
  (V : hSet ℓ-zero) where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base V
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base V

open Functor
open NatTrans

------------------------------------------------------------------------
-- Interaction laws
------------------------------------------------------------------------

{- Reading a location and writing its current value has no effect.

  get i (λ b → set i b t) = t
-}
get-set-currentᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (t : Γ ⊢ T .F-ob A) →
  getᵗ i (set-current-contᵗ i t) ≡ t
get-set-currentᵗ i t =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ (get-set-current-run i t n γ))

{- Reading immediately after writing returns the written value.

  set i b (get i k) = set i b (k b)
-}
set-get-sameᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b : Γ ⊢ VVal)
  (k : Γ CC.× VVal ⊢ T .F-ob A) →
  set-get-same-lhsᵗ i b k ≡ set-currentᵗ i b k
set-get-sameᵗ i b k =
  makeNatTransPath (funExt λ n → funExt λ γ → funExt₃ λ m n≤m σ →
    set-get-same-lhsᵗ-run i b k n γ m n≤m σ
    ∙ sym (set-currentᵗ-run i b k n γ m n≤m σ))

{- A later write to the same location overwrites an earlier write.

  set i b (set i c t) = set i c t
-}
set-set-sameᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b c : Γ ⊢ VVal) (t : Γ ⊢ T .F-ob A) →
  set-set-same-lhsᵗ i b c t ≡ setᵗ i c t
set-set-sameᵗ {A = A} i b c t =
  makeNatTransPath (funExt λ n → funExt λ γ → funExt₃ λ m n≤m σ →
    set-set-same-lhsᵗ-run i b c t n γ m n≤m σ
    ∙ cong (t .N-ob n γ m n≤m)
        (update-overwrite {n = m} (weakenRef n≤m (i .N-ob n γ))
          (b .N-ob n γ) (c .N-ob n γ) σ)
    ∙ sym (setᵗ-run {A = A} i c t n γ m n≤m σ))

------------------------------------------------------------------------
-- Commutativity laws
------------------------------------------------------------------------

{- Two reads commute; no distinctness assumption is required.

  get i (λ b → get j (λ c → k b c))
    = get j (λ c → get i (λ b → k b c))
-}
get-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref)
  (k : (Γ CC.× VVal) CC.× VVal ⊢ T .F-ob A) →
  getᵗ i (left-read-contᵗ j k) ≡
  getᵗ j (right-read-contᵗ i k)
get-get-commuteᵗ {Γ = Γ} {A = A} i j k =
  makeNatTransPath (funExt λ n → funExt λ γ → funExt₃ λ m n≤m σ →
    let
      γₘ : Γ .F-ob m .fst
      γₘ = Γ .F-hom n≤m γ
      vi : V .fst
      vi = lookupStore {n = m}
        (weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)) σ
      vj : V .fst
      vj = lookupStore {n = m}
        (weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)) σ
    in
    getᵗ-run {A = A} i (left-read-contᵗ j k) n γ m n≤m σ
    ∙ left-read-contᵗ-run {Γ = Γ} {A = A} j k
        m (γₘ , vi) m ≤-refl σ
    ∙ cong (λ δ → k .N-ob m
        (δ , lookupStore {n = m}
          (weakenRef {n = m} {m = m} ≤-refl (j .N-ob m γₘ)) σ)
        m ≤-refl σ)
        (funExt⁻ ((Γ CC.× VVal) .F-id) (γₘ , vi))
    ∙ cong (λ c → k .N-ob m ((γₘ , vi) , c) m ≤-refl σ)
        (cong σ
          (funExt⁻ (Ref .F-id {x = m}) (j .N-ob m γₘ)
          ∙ funExt⁻ (j .N-hom n≤m) γ))
    ∙ sym (cong (λ b → k .N-ob m ((γₘ , b) , vj) m ≤-refl σ)
        (cong σ
          (funExt⁻ (Ref .F-id {x = m}) (i .N-ob m γₘ)
          ∙ funExt⁻ (i .N-hom n≤m) γ)))
    ∙ sym (cong (λ δ → k .N-ob m
        ((δ , lookupStore {n = m}
          (weakenRef {n = m} {m = m} ≤-refl (i .N-ob m γₘ)) σ) , vj)
        m ≤-refl σ) (funExt⁻ (Γ .F-id) γₘ))
    ∙ sym (right-read-contᵗ-run {Γ = Γ} {A = A} i k
        m (γₘ , vj) m ≤-refl σ)
    ∙ sym (getᵗ-run {A = A} j (right-read-contᵗ i k)
        n γ m n≤m σ))

{- Writes to distinct locations commute.

  set i b (set j c t) = set j c (set i b t)    when i ≢ j
-}
set-set-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref) → Distinctᵗ i j →
  (b c : Γ ⊢ VVal) (t : Γ ⊢ T .F-ob A) →
  set-set-commute-lhsᵗ i j b c t ≡ set-set-commute-rhsᵗ i j b c t
set-set-commuteᵗ i j i≢j b c t =
  makeNatTransPath (funExt λ n → funExt λ γ → funExt₃ λ m n≤m σ →
    set-set-commute-lhsᵗ-run i j b c t n γ m n≤m σ
    ∙ cong (t .N-ob n γ m n≤m)
        (update-commute {n = m}
          (weakenRef n≤m (i .N-ob n γ))
          (weakenRef n≤m (j .N-ob n γ))
          (weakenRef-distinct n≤m _ _ (i≢j n γ))
          (b .N-ob n γ) (c .N-ob n γ) σ)
    ∙ sym (set-set-commute-rhsᵗ-run i j b c t n γ m n≤m σ))

{- A write and a read at distinct locations commute.

  set i b (get j (λ c → k c))
    = get j (λ c → set i b (k c))        when i ≢ j
-}
set-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref) → Distinctᵗ i j →
  (b : Γ ⊢ VVal) (k : Γ CC.× VVal ⊢ T .F-ob A) →
  set-get-commute-lhsᵗ i j b k ≡
  set-get-commute-rhsᵗ i j b k
set-get-commuteᵗ {Γ = Γ} {A = A} i j i≢j b k =
  makeNatTransPath (funExt λ n → funExt λ γ → funExt₃ λ m n≤m σ →
    let
      γₘ : Γ .F-ob m .fst
      γₘ = Γ .F-hom n≤m γ
      wi : Fin m
      wi = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
      wj : Fin m
      wj = weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)
      σi : Fin m → V .fst
      σi = updateStore {n = m} wi (b .N-ob n γ) σ
      vj : V .fst
      vj = lookupStore {n = m} wj σ
      store-right≡left = cong₂
        (λ r v → updateStore {n = m} r v σ)
        (funExt⁻ (Ref .F-id {x = m}) (i .N-ob m γₘ)
          ∙ funExt⁻ (i .N-hom n≤m) γ)
        (funExt⁻ (b .N-hom n≤m) γ)
    in
    set-get-commute-lhsᵗ-run i j b k n γ m n≤m σ
    ∙ cong (λ v → k .N-ob m (γₘ , v) m ≤-refl σi)
        (lookup-update-diff {n = m} wi wj
          (weakenRef-distinct n≤m _ _ (i≢j n γ))
          (b .N-ob n γ) σ)
    ∙ cong (λ τ → k .N-ob m (γₘ , vj) m ≤-refl τ)
        (sym store-right≡left)
    ∙ sym (set-get-commute-rhsᵗ-run i j b k n γ m n≤m σ))
