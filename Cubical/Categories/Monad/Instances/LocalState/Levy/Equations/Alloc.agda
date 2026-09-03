open import Cubical.Data.Fin using (Fin ; flast)
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Nat.Order
  using (_≤_ ; ≤-refl ; ≤-trans ; ≤-sucℕ ; isProp≤)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet)
open import Cubical.Functions.FunExtEquiv using (funExt₃)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Alloc
  (V : hSet ℓ-zero) where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base V
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base V

open Functor
open NatTrans

------------------------------------------------------------------------
-- Allocation laws
------------------------------------------------------------------------

{- Writing the freshly allocated location replaces its initial value.

  alloc b (λ i → set i c (k i))
    = alloc c (λ i → k i)
-}
alloc-set-freshᵗ : ∀ {Γ A}
  (b c : Γ ⊢ VVal) (k : Γ CC.× Ref ⊢ T ⟅ A ⟆) →
  allocᵗ b (setᵗ varᵗ (wkᵗ c) k) ≡ allocᵗ c k
alloc-set-freshᵗ {Γ = Γ} {A = A} b c k =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ λ m n≤m σ →
      let
        q : n ≤ suc m
        q = ≤-trans n≤m ≤-sucℕ
        γ⁺ : (Γ ⟅ suc m ⟆) .fst
        γ⁺ = Γ .F-hom q γ
        fresh : Fin (suc m)
        fresh = flast {k = m}
        τ : Fin (suc m) → V .fst
        τ = extendStore {n = m} (b .N-ob n γ) σ
        store-path =
          cong (λ r → updateStore {n = suc m} r
            (c .N-ob (suc m) γ⁺) τ)
            (funExt⁻ (Ref .F-id {x = suc m}) fresh)
          ∙ update-fresh {n = m}
              (b .N-ob n γ) (c .N-ob (suc m) γ⁺) σ
          ∙ cong (λ v → extendStore {n = m} v σ)
              (funExt⁻ (c .N-hom q) γ)
      in
      allocᵗ-β {Γ = Γ} {A = A} b
        (setᵗ varᵗ (wkᵗ c) k) n γ m n≤m σ
      ∙ cong (extendResult A ≤-sucℕ)
          (setᵗ-β {Γ = Γ CC.× Ref} {A = A}
            varᵗ (wkᵗ c) k
            (suc m) (γ⁺ , fresh) (suc m) ≤-refl τ)
      ∙ cong (extendResult A ≤-sucℕ)
          (cong (λ υ → k .N-ob (suc m) (γ⁺ , fresh)
            (suc m) ≤-refl υ) store-path)
      ∙ sym (allocᵗ-β {Γ = Γ} {A = A} c k n γ m n≤m σ))

{- Reading the freshly allocated location returns its initial value.

  alloc b (λ i → get i (λ c → k i c))
    = alloc b (λ i → k i b)
-}
alloc-get-freshᵗ : ∀ {Γ A}
  (b : Γ ⊢ VVal)
  (k : (Γ CC.× Ref) CC.× VVal ⊢ T ⟅ A ⟆) →
  allocᵗ b (getᵗ varᵗ k) ≡ allocᵗ b (k [ wkᵗ b ]ᵗ)
alloc-get-freshᵗ {Γ = Γ} {A = A} b k =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ λ m n≤m σ →
      let
        q : n ≤ suc m
        q = ≤-trans n≤m ≤-sucℕ
        γ⁺ : (Γ ⟅ suc m ⟆) .fst
        γ⁺ = Γ .F-hom q γ
        fresh : Fin (suc m)
        fresh = flast {k = m}
        bₙ : V .fst
        bₙ = b .N-ob n γ
        τ : Fin (suc m) → V .fst
        τ = extendStore {n = m} bₙ σ
        value-path =
          cong (λ r → lookupStore {n = suc m} r τ)
            (funExt⁻ (Ref .F-id {x = suc m}) fresh)
          ∙ extendStore-fresh {n = m} bₙ σ
          ∙ sym (funExt⁻ (b .N-hom q) γ)
      in
      allocᵗ-β {Γ = Γ} {A = A} b (getᵗ varᵗ k)
        n γ m n≤m σ
      ∙ cong (extendResult A ≤-sucℕ)
          (getᵗ-β {Γ = Γ CC.× Ref} {A = A} varᵗ k
            (suc m) (γ⁺ , fresh) (suc m) ≤-refl τ)
      ∙ cong (extendResult A ≤-sucℕ)
          (cong (λ δ → k .N-ob (suc m)
            (δ , lookupStore {n = suc m}
              (weakenRef {n = suc m} {m = suc m} ≤-refl fresh) τ)
            (suc m) ≤-refl τ)
            (funExt⁻ ((Γ CC.× Ref) .F-id) (γ⁺ , fresh)))
      ∙ cong (extendResult A ≤-sucℕ)
          (cong (λ v → k .N-ob (suc m) ((γ⁺ , fresh) , v)
            (suc m) ≤-refl τ) value-path)
      ∙ sym (allocᵗ-β {Γ = Γ} {A = A} b (k [ wkᵗ b ]ᵗ)
          n γ m n≤m σ))

{- Allocation commutes with writing an existing location `j`.

  alloc b (λ i → set j c (k i))
    = set j c (alloc b (λ i → k i))
-}
alloc-set-oldᵗ : ∀ {Γ A}
  (j : Γ ⊢ Ref) (b c : Γ ⊢ VVal)
  (k : Γ CC.× Ref ⊢ T ⟅ A ⟆) →
  allocᵗ b (setᵗ (wkᵗ j) (wkᵗ c) k) ≡
  setᵗ j c (allocᵗ b k)
alloc-set-oldᵗ {Γ = Γ} {A = A} j b c k =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ λ m n≤m σ →
      let
        q : n ≤ suc m
        q = ≤-trans n≤m ≤-sucℕ
        γ⁺ : (Γ ⟅ suc m ⟆) .fst
        γ⁺ = Γ .F-hom q γ
        fresh : Fin (suc m)
        fresh = flast {k = m}
        wj : Fin m
        wj = weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)
        rj≡old =
          funExt⁻ (Ref .F-id {x = suc m}) (j .N-ob (suc m) γ⁺)
          ∙ funExt⁻ (j .N-hom q) γ
          ∙ sym (weakenRef-comp n≤m ≤-sucℕ (j .N-ob n γ))
        store-path =
          cong₂
            (λ r v → updateStore {n = suc m} r v
              (extendStore {n = m} (b .N-ob n γ) σ))
            rj≡old (funExt⁻ (c .N-hom q) γ)
          ∙ update-extendStore-old {n = m}
              wj (b .N-ob n γ) (c .N-ob n γ) σ
      in
      allocᵗ-β {Γ = Γ} {A = A}
        b (setᵗ (wkᵗ j) (wkᵗ c) k) n γ m n≤m σ
      ∙ cong (extendResult A ≤-sucℕ)
          (setᵗ-β {Γ = Γ CC.× Ref} {A = A}
            (wkᵗ j) (wkᵗ c) k
            (suc m) (γ⁺ , fresh) (suc m) ≤-refl
            (extendStore {n = m} (b .N-ob n γ) σ))
      ∙ cong (extendResult A ≤-sucℕ)
          (cong (λ τ → k .N-ob (suc m) (γ⁺ , fresh)
            (suc m) ≤-refl τ) store-path)
      ∙ sym (allocᵗ-β {Γ = Γ} {A = A} b k n γ m n≤m
          (updateStore {n = m} wj (c .N-ob n γ) σ))
      ∙ sym (setᵗ-β {Γ = Γ} {A = A}
          j c (allocᵗ b k) n γ m n≤m σ))

{- Allocation commutes with reading an existing location `j`.

  alloc b (λ i → get j (λ c → k i c))
    = get j (λ c → alloc b (λ i → k i c))
-}
alloc-get-oldᵗ : ∀ {Γ A}
  (j : Γ ⊢ Ref) (b : Γ ⊢ VVal)
  (k : (Γ CC.× Ref) CC.× VVal ⊢ T ⟅ A ⟆) →
  allocᵗ b (getᵗ (wkᵗ j) k) ≡
  getᵗ j (allocᵗ (wkᵗ b) (exchangeᵗ k))
alloc-get-oldᵗ {Γ = Γ} {A = A} j b k =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ λ m n≤m σ →
      let
        q : n ≤ suc m
        q = ≤-trans n≤m ≤-sucℕ
        γₘ : (Γ ⟅ m ⟆) .fst
        γₘ = Γ .F-hom n≤m γ
        γ⁺ : (Γ ⟅ suc m ⟆) .fst
        γ⁺ = Γ .F-hom q γ
        fresh : Fin (suc m)
        fresh = flast {k = m}
        wj : Fin m
        wj = weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)
        bₙ : V .fst
        bₙ = b .N-ob n γ
        τ : Fin (suc m) → V .fst
        τ = extendStore {n = m} bₙ σ
        vj : V .fst
        vj = lookupStore {n = m} wj σ
        value-path =
          cong (λ r → lookupStore {n = suc m} r τ)
            (funExt⁻ (Ref .F-id {x = suc m})
                (j .N-ob (suc m) γ⁺)
            ∙ funExt⁻ (j .N-hom q) γ
            ∙ sym (weakenRef-comp n≤m ≤-sucℕ
                (j .N-ob n γ)))
          ∙ lookup-extendStore-old {n = m} wj bₙ σ
        rhs-step : m ≤ suc m
        rhs-step = ≤-trans ≤-refl ≤-sucℕ
        lifted-b : Γ CC.× VVal ⊢ VVal
        lifted-b = wkᵗ b
        rhs-context : ((Γ CC.× VVal) ⟅ suc m ⟆) .fst
        rhs-context =
          (Γ CC.× VVal) .F-hom rhs-step (γₘ , vj)
        rhs-store : Fin (suc m) → V .fst
        rhs-store = extendStore {n = m}
          (lifted-b .N-ob m (γₘ , vj)) σ
        alignment-path :
          extendResult A ≤-sucℕ
            (k .N-ob (suc m) ((γ⁺ , fresh) , vj)
              (suc m) ≤-refl τ) ≡
          extendResult A ≤-sucℕ
            ((exchangeᵗ k) .N-ob (suc m)
              (rhs-context , fresh) (suc m) ≤-refl rhs-store)
        alignment-path =
          cong (extendResult A ≤-sucℕ)
            (cong₂
              (λ δ υ → k .N-ob (suc m) ((δ , fresh) , vj)
                (suc m) ≤-refl υ)
              (funExt⁻ (Γ .F-seq n≤m ≤-sucℕ) γ
                ∙ cong (λ e → Γ .F-hom e γₘ)
                    (isProp≤ ≤-sucℕ rhs-step))
              (cong (λ v → extendStore {n = m} v σ)
                (sym (funExt⁻ (b .N-hom n≤m) γ))))
      in
      allocᵗ-β {Γ = Γ} {A = A} b (getᵗ (wkᵗ j) k)
        n γ m n≤m σ
      ∙ cong (extendResult A ≤-sucℕ)
          (getᵗ-β {Γ = Γ CC.× Ref} {A = A}
            (wkᵗ j) k
            (suc m) (γ⁺ , fresh) (suc m) ≤-refl τ)
      ∙ cong (extendResult A ≤-sucℕ)
          (cong
            (λ δ → k .N-ob (suc m)
              (δ , lookupStore {n = suc m}
                (weakenRef {n = suc m} {m = suc m} ≤-refl
                  (j .N-ob (suc m) γ⁺)) τ)
              (suc m) ≤-refl τ)
            (funExt⁻ ((Γ CC.× Ref) .F-id) (γ⁺ , fresh)))
      ∙ cong (extendResult A ≤-sucℕ)
          (cong
            (λ v → k .N-ob (suc m) ((γ⁺ , fresh) , v)
              (suc m) ≤-refl τ)
            value-path)
      ∙ alignment-path
      ∙ sym (allocᵗ-β {Γ = Γ CC.× VVal} {A = A}
          (wkᵗ b) (exchangeᵗ k) m (γₘ , vj) m ≤-refl σ)
      ∙ sym (getᵗ-β {Γ = Γ} {A = A} j
          (allocᵗ (wkᵗ b) (exchangeᵗ k)) n γ m n≤m σ))

------------------------------------------------------------------------
-- Unsupported block laws
------------------------------------------------------------------------

{- Garbage collection would assert

     alloc b (λ _ → t) = t.

   This is not an equality in the present monad. Allocation returns a
   computation whose result world contains one additional cell. The result
   type records that world explicitly, so a computation returning world
   `suc m` cannot equal one returning world `m`, even when the fresh reference
   and its store cell are never subsequently observed.
-}

{- Exchange of two fresh allocations would assert

     alloc b (λ i → alloc c (λ j → k i j))
       = alloc c (λ j → alloc b (λ i → k i j)).

   Both sides return `suc (suc m)`, but they assign the two concrete final
   positions in opposite orders. `World` is the preorder of natural numbers
   and extensions; it has no permutation morphisms. Consequently there is
   no renaming which exchanges the two fresh `Fin` positions and the matching
   store cells, so the two computations are not equal in general.
-}
