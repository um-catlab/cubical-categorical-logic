module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.AllocGetOld where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Discrete
open import Cubical.Data.Fin
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Nat.Order
  using (_≤_ ; ≤-refl ; ≤-trans ; ≤-sucℕ ; isProp≤)
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt

open Functor
open NatTrans
open PshHom

{- Allocation commutes with reading an already existing location j.

  alloc b (λ i → get j (λ c → k i c))
    = get j (λ c → alloc b (λ i → k i c))
-}
alloc-get-oldᵗ : ∀ {Γ A}
  (j : Γ ⊢ Ref) (b : Γ ⊢ BoolVal)
  (k : (Γ V.× Ref) V.× BoolVal ⊢ T .F-ob A) →
  allocᵗ b (getᵗ (V.π₁ V.⋆ j) k) ≡
  getᵗ j (allocᵗ (V.π₁ V.⋆ b) (swapLast V.⋆ k))
alloc-get-oldᵗ {Γ = Γ} {A = A} j b k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext {A = A} λ m n≤m σ →
    let
      q : n ≤ suc m
      q = ≤-trans n≤m ≤-sucℕ
      γₘ : Γ .F-ob m .fst
      γₘ = Γ .F-hom n≤m γ
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
      bₙ : Bool
      bₙ = b .N-ob n γ
      τ : Fin (suc m) → Bool
      τ = extendStore {n = m} bₙ σ
      vj : Bool
      vj = lookupStore {n = m} wj σ
      rj≡old =
        funExt⁻ (Ref .F-id {x = suc m}) j⁺
        ∙ funExt⁻ (j .N-hom q) γ
        ∙ sym (weakenRef-comp n≤m ≤-sucℕ (j .N-ob n γ))
      value-path =
        cong (λ r → lookupStore {n = suc m} r τ) rj≡old
        ∙ alloc-get-distinct {n = m} wj bₙ σ
      context-id = funExt⁻ ((Γ V.× Ref) .F-id) (γ⁺ , fresh)
      γ-path = funExt⁻ (Γ .F-seq n≤m ≤-sucℕ) γ
      b-path = funExt⁻ (b .N-hom n≤m) γ
      store-path = cong (λ v → extendStore {n = m} v σ) (sym b-path)
      rhs-step : m ≤ suc m
      rhs-step = ≤-trans ≤-refl ≤-sucℕ
      lifted-b : (Γ V.× BoolVal) ⊢ BoolVal
      lifted-b = V.π₁ V.⋆ b
      rhs-context : (Γ V.× BoolVal) .F-ob (suc m) .fst
      rhs-context = (Γ V.× BoolVal) .F-hom rhs-step (γₘ , vj)
      rhs-store : Fin (suc m) → Bool
      rhs-store = extendStore {n = m}
        (lifted-b .N-ob m (γₘ , vj)) σ
      rhs-γ-path = cong (λ e → Γ .F-hom e γₘ)
        (isProp≤ ≤-sucℕ rhs-step)
      alignment-path :
        extendResult A ≤-sucℕ
          (k .N-ob (suc m) ((γ⁺ , fresh) , vj)
            (suc m) ≤-refl τ) ≡
        extendResult A ≤-sucℕ
          ((swapLast V.⋆ k) .N-ob (suc m)
            (rhs-context , fresh) (suc m) ≤-refl rhs-store)
      alignment-path = cong (extendResult A ≤-sucℕ)
        (cong₂
          (λ δ υ → k .N-ob (suc m) ((δ , fresh) , vj)
            (suc m) ≤-refl υ)
          (γ-path ∙ rhs-γ-path) store-path)
    in
    allocᵗ-run {A = A} b (getᵗ (V.π₁ V.⋆ j) k) n γ m n≤m σ
    ∙ cong (extendResult A ≤-sucℕ)
        (getᵗ-run {A = A} (V.π₁ V.⋆ j) k
          (suc m) (γ⁺ , fresh) (suc m) ≤-refl τ)
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ δ → k .N-ob (suc m)
          (δ , lookupStore {n = suc m} rj τ)
          (suc m) ≤-refl τ) context-id)
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ v → k .N-ob (suc m) ((γ⁺ , fresh) , v)
          (suc m) ≤-refl τ) value-path)
    ∙ alignment-path
    ∙ sym (allocᵗ-run {A = A} lifted-b (swapLast V.⋆ k)
        m (γₘ , vj) m ≤-refl σ)
    ∙ sym (getᵗ-run {A = A} j
        (allocᵗ lifted-b (swapLast V.⋆ k))
        n γ m n≤m σ))

------------------------------------------------------------------------
-- Why the block-commutative laws fail here
------------------------------------------------------------------------

{- Garbage collection would assert

     alloc b (λ _ → t) = t.

   This is not an equality in the present monad.  Allocation returns a
   computation whose result world contains one additional cell.  The result
   type records that world explicitly, so a computation returning world
   `suc m` cannot equal one returning world `m`, even when the fresh reference
   and its store cell are never subsequently observed.
-}

{- Exchange of two fresh allocations would assert

     alloc b (λ i → alloc c (λ j → k i j))
       = alloc c (λ j → alloc b (λ i → k i j)).

   Both sides return `suc (suc m)`, but they assign the two concrete final
   positions in opposite orders.  `World` is the preorder of natural numbers
   and extensions; it has no permutation morphisms.  Consequently there is
   no renaming which exchanges the two fresh `Fin` positions and the matching
   store cells, so the two computations are not equal in general.
-}
