open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Nat.Order using (≤-refl ; isProp≤)
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
  (i : Γ ⊢ Ref) (t : Γ ⊢ T ⟅ A ⟆) →
  getᵗ i (setᵗ (wkᵗ i) varᵗ (wkᵗ t)) ≡ t
get-set-currentᵗ {Γ = Γ} {A = A} i t =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ λ m n≤m σ →
      let
        γₘ : (Γ ⟅ m ⟆) .fst
        γₘ = Γ .F-hom n≤m γ
      in
      getᵗ-β {Γ = Γ} {A = A} i
        (setᵗ (wkᵗ i) varᵗ (wkᵗ t)) n γ m n≤m σ
      ∙ setᵗ-β {Γ = Γ CC.× VVal} {A = A}
          (wkᵗ i) varᵗ (wkᵗ t)
          m (γₘ , lookupStore {n = m}
            (weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)) σ)
          m ≤-refl σ
      ∙ cong (λ τ → t .N-ob m γₘ m ≤-refl τ)
          (get-set-current-store i γ n≤m σ)
      ∙ cong (λ u → u m ≤-refl σ)
          (funExt⁻ (t .N-hom n≤m) γ)
      ∙ cong (λ q → t .N-ob n γ m q σ) (isProp≤ _ _))

{- Reading immediately after writing returns the written value.

  set i b (get i k) = set i b (k b)
-}
set-get-sameᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b : Γ ⊢ VVal)
  (k : Γ CC.× VVal ⊢ T ⟅ A ⟆) →
  setᵗ i b (getᵗ i k) ≡ setᵗ i b (k [ b ]ᵗ)
set-get-sameᵗ {Γ = Γ} {A = A} i b k =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ λ m n≤m σ →
      let
        r : Fin m
        r = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
        v : V .fst
        v = b .N-ob n γ
        σ′ : Fin m → V .fst
        σ′ = updateStore {n = m} r v σ
      in
      setᵗ-β {Γ = Γ} {A = A} i b (getᵗ i k) n γ m n≤m σ
      ∙ getᵗ-β {Γ = Γ} {A = A} i k n γ m n≤m σ′
      ∙ cong (λ c → k .N-ob m (Γ .F-hom n≤m γ , c) m ≤-refl σ′)
          (lookup-update-same {n = m} r v σ)
      ∙ cong (λ u → u m ≤-refl σ′)
          (funExt⁻ (k .N-hom n≤m) (γ , v))
      ∙ cong (λ q → k .N-ob n (γ , v) m q σ′) (isProp≤ _ _)
      ∙ sym (setᵗ-β {Γ = Γ} {A = A} i b (k [ b ]ᵗ)
          n γ m n≤m σ))

{- A later write to the same location overwrites an earlier write.

  set i b (set i c t) = set i c t
-}
set-set-sameᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b c : Γ ⊢ VVal) (t : Γ ⊢ T ⟅ A ⟆) →
  setᵗ i b (setᵗ i c t) ≡ setᵗ i c t
set-set-sameᵗ {Γ = Γ} {A = A} i b c t =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ λ m n≤m σ →
      let
        r : Fin m
        r = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
        vb : V .fst
        vb = b .N-ob n γ
      in
      setᵗ-β {Γ = Γ} {A = A} i b (setᵗ i c t) n γ m n≤m σ
      ∙ setᵗ-β {Γ = Γ} {A = A} i c t n γ m n≤m
          (updateStore {n = m} r vb σ)
      ∙ cong (t .N-ob n γ m n≤m)
          (update-overwrite {n = m} r vb (c .N-ob n γ) σ)
      ∙ sym (setᵗ-β {Γ = Γ} {A = A} i c t n γ m n≤m σ))

------------------------------------------------------------------------
-- Commutativity laws
------------------------------------------------------------------------

{- Two reads commute; no distinctness assumption is required.

  get i (λ b → get j (λ c → k b c))
    = get j (λ c → get i (λ b → k b c))
-}
get-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref)
  (k : (Γ CC.× VVal) CC.× VVal ⊢ T ⟅ A ⟆) →
  getᵗ i (getᵗ (wkᵗ j) k) ≡
  getᵗ j (getᵗ (wkᵗ i) (exchangeᵗ k))
get-get-commuteᵗ {Γ = Γ} {A = A} i j k =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ λ m n≤m σ →
      let
        γₘ : (Γ ⟅ m ⟆) .fst
        γₘ = Γ .F-hom n≤m γ
        vi : V .fst
        vi = lookupStore {n = m}
          (weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)) σ
        vj : V .fst
        vj = lookupStore {n = m}
          (weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)) σ
      in
      getᵗ-β {Γ = Γ} {A = A} i (getᵗ (wkᵗ j) k) n γ m n≤m σ
      ∙ getᵗ-β {Γ = Γ CC.× VVal} {A = A} (wkᵗ j) k
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
          m ≤-refl σ)
          (funExt⁻ (Γ .F-id) γₘ))
      ∙ sym (getᵗ-β {Γ = Γ CC.× VVal} {A = A}
          (wkᵗ i) (exchangeᵗ k) m (γₘ , vj) m ≤-refl σ)
      ∙ sym (getᵗ-β {Γ = Γ} {A = A} j
          (getᵗ (wkᵗ i) (exchangeᵗ k)) n γ m n≤m σ))

{- Writes to distinct locations commute.

  set i b (set j c t) = set j c (set i b t)    when i ≢ j
-}
set-set-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref) → Distinctᵗ i j →
  (b c : Γ ⊢ VVal) (t : Γ ⊢ T ⟅ A ⟆) →
  setᵗ i b (setᵗ j c t) ≡ setᵗ j c (setᵗ i b t)
set-set-commuteᵗ {Γ = Γ} {A = A} i j i≢j b c t =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ λ m n≤m σ →
      let
        wi : Fin m
        wi = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
        wj : Fin m
        wj = weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)
        vb : V .fst
        vb = b .N-ob n γ
        vc : V .fst
        vc = c .N-ob n γ
      in
      setᵗ-β {Γ = Γ} {A = A} i b (setᵗ j c t) n γ m n≤m σ
      ∙ setᵗ-β {Γ = Γ} {A = A} j c t n γ m n≤m
          (updateStore {n = m} wi vb σ)
      ∙ cong (t .N-ob n γ m n≤m)
          (update-commute {n = m} wi wj
            (weakenRef-distinct n≤m _ _ (i≢j n γ)) vb vc σ)
      ∙ sym (setᵗ-β {Γ = Γ} {A = A} i b t n γ m n≤m
          (updateStore {n = m} wj vc σ))
      ∙ sym (setᵗ-β {Γ = Γ} {A = A} j c (setᵗ i b t)
          n γ m n≤m σ))

{- A write and a read at distinct locations commute.

  set i b (get j (λ c → k c))
    = get j (λ c → set i b (k c))        when i ≢ j
-}
set-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref) → Distinctᵗ i j →
  (b : Γ ⊢ VVal) (k : Γ CC.× VVal ⊢ T ⟅ A ⟆) →
  setᵗ i b (getᵗ j k) ≡
  getᵗ j (setᵗ (wkᵗ i) (wkᵗ b) k)
set-get-commuteᵗ {Γ = Γ} {A = A} i j i≢j b k =
  makeNatTransPath (funExt λ n → funExt λ γ →
    funExt₃ λ m n≤m σ →
      let
        γₘ : (Γ ⟅ m ⟆) .fst
        γₘ = Γ .F-hom n≤m γ
        wi : Fin m
        wi = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
        wj : Fin m
        wj = weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)
        vb : V .fst
        vb = b .N-ob n γ
        σi : Fin m → V .fst
        σi = updateStore {n = m} wi vb σ
        vj : V .fst
        vj = lookupStore {n = m} wj σ
        store-right≡left :
          updateStore {n = m}
            (weakenRef {n = m} {m = m} ≤-refl (i .N-ob m γₘ))
            (b .N-ob m γₘ) σ ≡ σi
        store-right≡left =
          cong₂ (λ r v → updateStore {n = m} r v σ)
            (funExt⁻ (Ref .F-id {x = m}) (i .N-ob m γₘ)
              ∙ funExt⁻ (i .N-hom n≤m) γ)
            (funExt⁻ (b .N-hom n≤m) γ)
      in
      setᵗ-β {Γ = Γ} {A = A} i b (getᵗ j k) n γ m n≤m σ
      ∙ getᵗ-β {Γ = Γ} {A = A} j k n γ m n≤m σi
      ∙ cong (λ v → k .N-ob m (γₘ , v) m ≤-refl σi)
          (lookup-update-diff {n = m} wi wj
            (weakenRef-distinct n≤m _ _ (i≢j n γ)) vb σ)
      ∙ cong (λ τ → k .N-ob m (γₘ , vj) m ≤-refl τ)
          (sym store-right≡left)
      ∙ sym (setᵗ-β {Γ = Γ CC.× VVal} {A = A}
          (wkᵗ i) (wkᵗ b) k m (γₘ , vj) m ≤-refl σ)
      ∙ sym (getᵗ-β {Γ = Γ} {A = A} j
          (setᵗ (wkᵗ i) (wkᵗ b) k) n γ m n≤m σ))
