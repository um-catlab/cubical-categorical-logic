module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.SetGetCommute where

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

{- A write and a read at distinct locations commute.

  set i b (get j (λ c → k c))
    = get j (λ c → set i b (k c))        when i ≢ j
-}
opaque
  read-contᵗ : ∀ {Γ A} →
    (j : Γ ⊢ Ref) (k : Γ V.× BoolVal ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  read-contᵗ = getᵗ

  read-contᵗ-run : ∀ {Γ A}
    (j : Γ ⊢ Ref) (k : Γ V.× BoolVal ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → Bool) →
    read-contᵗ j k .N-ob n γ m n≤m σ ≡
    k .N-ob m
      (Γ .F-hom n≤m γ ,
       lookupStore {n = m} (weakenRef n≤m (j .N-ob n γ)) σ)
      m ≤-refl σ
  read-contᵗ-run {A = A} j k n γ m n≤m σ =
    getᵗ-run {A = A} j k n γ m n≤m σ

opaque
  set-read-contᵗ : ∀ {Γ A} →
    (i : Γ ⊢ Ref) (b : Γ ⊢ BoolVal)
    (k : Γ V.× BoolVal ⊢ T .F-ob A) →
    Γ V.× BoolVal ⊢ T .F-ob A
  set-read-contᵗ i b k =
    setᵗ (V.π₁ V.⋆ i) (V.π₁ V.⋆ b) k

  set-read-contᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (b : Γ ⊢ BoolVal)
    (k : Γ V.× BoolVal ⊢ T .F-ob A)
    n (δ : (Γ V.× BoolVal) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → Bool) →
    set-read-contᵗ i b k .N-ob n δ m n≤m σ ≡
    k .N-ob n δ m n≤m
      (updateStore {n = m}
        (weakenRef n≤m (i .N-ob n (δ .fst)))
        (b .N-ob n (δ .fst)) σ)
  set-read-contᵗ-run {A = A} i b k n δ m n≤m σ =
    setᵗ-run {A = A} (V.π₁ V.⋆ i) (V.π₁ V.⋆ b) k
      n δ m n≤m σ

set-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref) → Distinctᵗ i j →
  (b : Γ ⊢ BoolVal) (k : Γ V.× BoolVal ⊢ T .F-ob A) →
  setᵗ i b (read-contᵗ j k) ≡
  getᵗ j (set-read-contᵗ i b k)
set-get-commuteᵗ {Γ = Γ} {A = A} i j i≢j b k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      γₘ : Γ .F-ob m .fst
      γₘ = Γ .F-hom n≤m γ
      wi : Fin m
      wi = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
      wj : Fin m
      wj = weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)
      bv : Bool
      bv = b .N-ob n γ
      σi : Fin m → Bool
      σi = updateStore {n = m} wi bv σ
      vj : Bool
      vj = lookupStore {n = m} wj σ
      iₘ : Fin m
      iₘ = i .N-ob m γₘ
      ri : Fin m
      ri = weakenRef {n = m} {m = m} ≤-refl iₘ
      bm : Bool
      bm = b .N-ob m γₘ
      ri≡wi = funExt⁻ (Ref .F-id {x = m}) iₘ ∙ funExt⁻ (i .N-hom n≤m) γ
      bm≡bv = funExt⁻ (b .N-hom n≤m) γ
      store-right≡left = cong₂
        (λ r v → updateStore {n = m} r v σ) ri≡wi bm≡bv
    in
    setᵗ-run {A = A} i b (read-contᵗ j k) n γ m n≤m σ
    ∙ read-contᵗ-run j k n γ m n≤m σi
    ∙ cong (λ v → k .N-ob m (γₘ , v) m ≤-refl σi)
        (lookup-update-diff {n = m} wi wj
          (weakenRef-distinct n≤m _ _ (i≢j n γ)) bv σ)
    ∙ cong (λ τ → k .N-ob m (γₘ , vj) m ≤-refl τ)
        (sym store-right≡left)
    ∙ sym (set-read-contᵗ-run i b k m (γₘ , vj) m ≤-refl σ)
    ∙ sym (getᵗ-run {A = A} j (set-read-contᵗ i b k)
        n γ m n≤m σ))

------------------------------------------------------------------------
