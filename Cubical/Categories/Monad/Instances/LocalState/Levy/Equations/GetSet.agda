module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.GetSet where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.PiSigma
open import Cubical.Data.Fin
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
open import Cubical.Data.Nat.Order using (_≤_ ; ≤-refl ; isProp≤)
open import Cubical.Foundations.Prelude
open import Cubical.Functions.FunExtEquiv using (funExt₃)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt

open Functor
open NatTrans
open PshHom

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
  (i : Γ ⊢ Ref) (b : Γ ⊢ BoolVal)
  (k : Γ V.× BoolVal ⊢ T .F-ob A) →
  setᵗ i b (getᵗ i k) ≡ setᵗ i b ((V.id V.,p b) V.⋆ k)
set-get-sameᵗ {Γ = Γ} i b k =
  makeNatTransPath (funExt λ n → funExt λ γ → funExt₃ λ m n≤m σ →
    let
      σ' : Fin m → Bool
      σ' = updateStore {n = m}
        (weakenRef n≤m (i .N-ob n γ)) (b .N-ob n γ) σ
    in
    setᵗ-run i b (getᵗ i k) n γ m n≤m σ
    ∙ getᵗ-run i k n γ m n≤m σ'
    ∙ cong (λ c → k .N-ob m (Γ .F-hom n≤m γ , c)
        m ≤-refl σ')
        (lookup-update-same {n = m}
          (weakenRef n≤m (i .N-ob n γ)) (b .N-ob n γ) σ)
    ∙ cong (λ u → u m ≤-refl σ')
        (funExt⁻ (k .N-hom n≤m) (γ , b .N-ob n γ))
    ∙ cong (λ q → k .N-ob n (γ , b .N-ob n γ) m q σ')
        (isProp≤ _ _)
    ∙ sym (setᵗ-current-run i b k n γ m n≤m σ))

{- A later write to the same location overwrites an earlier write.

  set i b (set i c t) = set i c t
-}
set-set-sameᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b c : Γ ⊢ BoolVal) (t : Γ ⊢ T .F-ob A) →
  setᵗ i b (setᵗ i c t) ≡ setᵗ i c t
set-set-sameᵗ {Γ = Γ} {A = A} i b c t =
  makeNatTransPath (funExt λ n → funExt λ γ → funExt₃ λ m n≤m σ →
    setᵗ-run {A = A} i b (setᵗ i c t) n γ m n≤m σ
    ∙ setᵗ-run {A = A} i c t n γ m n≤m
        (updateStore {n = m}
          (weakenRef n≤m (i .N-ob n γ)) (b .N-ob n γ) σ)
    ∙ cong (t .N-ob n γ m n≤m)
        (update-overwrite {n = m} (weakenRef n≤m (i .N-ob n γ))
          (b .N-ob n γ) (c .N-ob n γ) σ)
    ∙ sym (setᵗ-run {A = A} i c t n γ m n≤m σ))

------------------------------------------------------------------------
-- Commutativity laws
------------------------------------------------------------------------

{- Reads commute. No distinctness assumption is required.

  get i (λ b → get j (λ c → k b c))
    = get j (λ c → get i (λ b → k b c))
-}
get-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref)
  (k : (Γ V.× BoolVal) V.× BoolVal ⊢ T .F-ob A) →
  getᵗ i (left-read-contᵗ j k) ≡
  getᵗ j (right-read-contᵗ i k)
get-get-commuteᵗ {Γ = Γ} {A = A} i j k =
  makeNatTransPath (funExt λ n → funExt λ γ → funExt₃ λ m n≤m σ →
    let
      γₘ : Γ .F-ob m .fst
      γₘ = Γ .F-hom n≤m γ
      vi : Bool
      vi = lookupStore {n = m}
        (weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)) σ
      vj : Bool
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
        (funExt⁻ ((Γ V.× BoolVal) .F-id) (γₘ , vi))
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
  (b c : Γ ⊢ BoolVal) (t : Γ ⊢ T .F-ob A) →
  setᵗ i b (setᵗ j c t) ≡ setᵗ j c (setᵗ i b t)
set-set-commuteᵗ {Γ = Γ} {A = A} i j i≢j b c t =
  makeNatTransPath (funExt λ n → funExt λ γ → funExt₃ λ m n≤m σ →
    setᵗ-run {A = A} i b (setᵗ j c t) n γ m n≤m σ
    ∙ setᵗ-run {A = A} j c t n γ m n≤m
        (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
          (b .N-ob n γ) σ)
    ∙ cong (t .N-ob n γ m n≤m)
        (update-commute {n = m}
          (weakenRef n≤m (i .N-ob n γ))
          (weakenRef n≤m (j .N-ob n γ))
          (weakenRef-distinct n≤m _ _ (i≢j n γ))
          (b .N-ob n γ) (c .N-ob n γ) σ)
    ∙ sym (setᵗ-run {A = A} i b t n γ m n≤m
        (updateStore {n = m} (weakenRef n≤m (j .N-ob n γ))
          (c .N-ob n γ) σ))
    ∙ sym (setᵗ-run {A = A} j c (setᵗ i b t) n γ m n≤m σ))

{- A write and a read at distinct locations commute.

  set i b (get j (λ c → k c))
    = get j (λ c → set i b (k c))        when i ≢ j
-}
set-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref) → Distinctᵗ i j →
  (b : Γ ⊢ BoolVal) (k : Γ V.× BoolVal ⊢ T .F-ob A) →
  setᵗ i b (getᵗ j k) ≡
  getᵗ j (set-read-contᵗ i b k)
set-get-commuteᵗ {Γ = Γ} {A = A} i j i≢j b k =
  makeNatTransPath (funExt λ n → funExt λ γ → funExt₃ λ m n≤m σ →
    let
      γₘ : Γ .F-ob m .fst
      γₘ = Γ .F-hom n≤m γ
      wi : Fin m
      wi = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
      wj : Fin m
      wj = weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)
      σi : Fin m → Bool
      σi = updateStore {n = m} wi (b .N-ob n γ) σ
      vj : Bool
      vj = lookupStore {n = m} wj σ
      store-right≡left = cong₂
        (λ r v → updateStore {n = m} r v σ)
        (funExt⁻ (Ref .F-id {x = m}) (i .N-ob m γₘ)
          ∙ funExt⁻ (i .N-hom n≤m) γ)
        (funExt⁻ (b .N-hom n≤m) γ)
    in
    setᵗ-run {A = A} i b (getᵗ j k) n γ m n≤m σ
    ∙ getᵗ-run {A = A} j k n γ m n≤m σi
    ∙ cong (λ v → k .N-ob m (γₘ , v) m ≤-refl σi)
        (lookup-update-diff {n = m} wi wj
          (weakenRef-distinct n≤m _ _ (i≢j n γ))
          (b .N-ob n γ) σ)
    ∙ cong (λ τ → k .N-ob m (γₘ , vj) m ≤-refl τ)
        (sym store-right≡left)
    ∙ sym (set-read-contᵗ-run i b k m (γₘ , vj) m ≤-refl σ)
    ∙ sym (getᵗ-run {A = A} j (set-read-contᵗ i b k)
        n γ m n≤m σ))

------------------------------------------------------------------------
