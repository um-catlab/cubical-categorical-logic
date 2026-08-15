module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations where

open import Cubical.Data.Sigma
open import Cubical.Data.Fin
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order
  using (_≤_ ; ≤-refl ; ≤-trans ; ≤-sucℕ ; isProp≤)
open import Cubical.Foundations.Prelude
open import Cubical.Functions.FunExtEquiv using (funExt₃)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Presheaf.CCC
open import Cubical.Categories.Presheaf.Constructions.Exponential
  using (_⇒PshLarge_)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Discrete

open Functor
open NatTrans
open PshHom

Val-CCC : CartesianClosedCategory _ _
Val-CCC = Cubical.Categories.Presheaf.CCC.𝓟-CCC (World ^op) ℓ-zero

module V = CartesianClosedCategory Val-CCC

-- Terms are natural transformations between value presheaves.  Keeping the
-- context explicit below lets the state operations be used under weakening.
infix 1 _⊢_
_⊢_ : V.ob → V.ob → Type _
Γ ⊢ A = V.C [ Γ , A ]

-- Algebraic operations in an arbitrary context.
getᵗ : ∀ {Γ A} →
  Γ ⊢ Ref →
  Γ V.× BoolVal ⊢ T .F-ob A →
  Γ ⊢ T .F-ob A
getᵗ {A = A} i k = (i V.,p V.lda k) V.⋆ get A

setᵗ : ∀ {Γ A} →
  Γ ⊢ Ref →
  Γ ⊢ BoolVal →
  Γ ⊢ T .F-ob A →
  Γ ⊢ T .F-ob A
setᵗ {A = A} i b t = ((i V.,p b) V.,p t) V.⋆ set A

allocᵗ : ∀ {Γ A} →
  Γ ⊢ BoolVal →
  Γ V.× Ref ⊢ T .F-ob A →
  Γ ⊢ T .F-ob A
allocᵗ {A = A} b k = (b V.,p V.lda k) V.⋆ alloc A

-- A computation started in world m may finish in a larger world p.  When the
-- same result is viewed from an earlier world, only its lower-bound witness
-- changes; the final world, value, and store are unchanged.
extendResult : (B : V.ob) {m p : ℕ} →
  m ≤ p → F .F-ob B .F-ob p .fst → F .F-ob B .F-ob m .fst
extendResult B m≤p (q , p≤q , b , υ) =
  q , ≤-trans m≤p p≤q , b , υ

extendResult-refl : (B : V.ob) {m : ℕ}
  (r : F .F-ob B .F-ob m .fst) → extendResult B ≤-refl r ≡ r
extendResult-refl B (q , m≤q , b , υ) =
  ΣPathP (refl , ΣPathP (isProp≤ _ _ , ΣPathP (refl , refl)))

-- Pointwise semantics of Kleisli extension: run t, feed its value and final
-- store to k at the world produced by t, then rebase the result to world m.
runBindT : (A B : V.ob) {n : ℕ} →
  T .F-ob A .F-ob n .fst →
  (A ⇒PshLarge (T .F-ob B)) .F-ob n .fst →
  T .F-ob B .F-ob n .fst
runBindT A B {n} t k m n≤m σ with t m n≤m σ
... | p , m≤p , a , τ =
  extendResult B m≤p
    (k .N-ob p (≤-trans n≤m m≤p , a) p ≤-refl τ)

bindT-run : ∀ (A B : V.ob) {n : ℕ}
  (t : T .F-ob A .F-ob n .fst)
  (k : (A ⇒PshLarge (T .F-ob B)) .F-ob n .fst)
  (m : ℕ) (n≤m : n ≤ m) (σ : Fin m → Bool) →
  bindT .N-ob n (t , k) m n≤m σ ≡ runBindT A B t k m n≤m σ
bindT-run A B {n} t k m n≤m σ with t m n≤m σ
... | p , m≤p , a , τ =
  cong (extendResult B m≤p)
    (cong
      (λ h → k .N-ob p (h , a) p ≤-refl τ)
      (isProp≤ _ _))

-- The following three lemmas expose the concrete store semantics hidden by
-- the definitions of the algebraic operations.  Subsequent equations reduce
-- to these rules plus the corresponding lookup/update laws from Discrete.
get-run : ∀ (A : V.ob) n
  (x : (Ref V.× (BoolVal V.⇒ (T .F-ob A))) .F-ob n .fst)
  m (n≤m : n ≤ m) (σ : Fin m → Bool) →
  get A .N-ob n x m n≤m σ ≡
  x .snd .N-ob m
    (n≤m , lookupStore {n = m} (weakenRef n≤m (x .fst)) σ)
    m ≤-refl σ
get-run A n (i , k) m n≤m σ =
  bindT-run BoolVal A
    (getM .N-ob n i) k m n≤m σ
  ∙ cong (extendResult A ≤-refl)
      (cong
        (λ h → k .N-ob m
          (h , lookupStore {n = m} (weakenRef n≤m i) σ)
          m ≤-refl σ)
        (isProp≤ _ _))
  ∙ extendResult-refl A
      (k .N-ob m
        (n≤m , lookupStore {n = m} (weakenRef n≤m i) σ)
        m ≤-refl σ)

ignoreUnit : (A : V.ob) → (T .F-ob A) ⊢ (UnitVal V.⇒ (T .F-ob A))
ignoreUnit A = V.lda V.π₁

set-run : ∀ (A : V.ob) n
  (x : ((Ref V.× BoolVal) V.× (T .F-ob A)) .F-ob n .fst)
  m (n≤m : n ≤ m) (σ : Fin m → Bool) →
  set A .N-ob n x m n≤m σ ≡
  x .snd m n≤m
    (updateStore {n = m} (weakenRef n≤m (x .fst .fst))
      (x .fst .snd) σ)
set-run A n ((i , b) , t) m n≤m σ =
  bindT-run UnitVal A
    (setM .N-ob n (i , b)) (ignoreUnit A .N-ob n t) m n≤m σ
  ∙ cong (extendResult A ≤-refl)
      (cong
        (λ h → t m h
          (updateStore {n = m} (weakenRef n≤m i) b σ))
        (isProp≤ _ _))
  ∙ extendResult-refl A
      (t m n≤m
        (updateStore {n = m} (weakenRef n≤m i) b σ))

alloc-run : ∀ (A : V.ob) n
  (x : (BoolVal V.× (Ref V.⇒ (T .F-ob A))) .F-ob n .fst)
  m (n≤m : n ≤ m) (σ : Fin m → Bool) →
  alloc A .N-ob n x m n≤m σ ≡
  extendResult A ≤-sucℕ
    (x .snd .N-ob (suc m)
      (≤-trans n≤m ≤-sucℕ , flast {k = m})
      (suc m) ≤-refl (extendStore {n = m} (x .fst) σ))
alloc-run A n (b , k) m n≤m σ =
  bindT-run Ref A (allocM .N-ob n b) k m n≤m σ

getᵗ-run : ∀ {Γ A}
  (i : Γ ⊢ Ref) (k : Γ V.× BoolVal ⊢ T .F-ob A)
  n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → Bool) →
  getᵗ i k .N-ob n γ m n≤m σ ≡
  k .N-ob m
    (Γ .F-hom n≤m γ ,
     lookupStore {n = m} (weakenRef n≤m (i .N-ob n γ)) σ)
    m ≤-refl σ
getᵗ-run {Γ = Γ} {A = A} i k n γ m n≤m σ =
  get-run A n (i .N-ob n γ , V.lda k .N-ob n γ) m n≤m σ
  ∙ cong
      (λ q → k .N-ob m
        (Γ .F-hom q γ ,
         lookupStore {n = m} (weakenRef n≤m (i .N-ob n γ)) σ)
        m ≤-refl σ)
      (isProp≤ _ _)

setᵗ-run : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b : Γ ⊢ BoolVal) (t : Γ ⊢ T .F-ob A)
  n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → Bool) →
  setᵗ i b t .N-ob n γ m n≤m σ ≡
  t .N-ob n γ m n≤m
    (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
      (b .N-ob n γ) σ)
setᵗ-run {A = A} i b t n γ m n≤m σ =
  set-run A n ((i .N-ob n γ , b .N-ob n γ) , t .N-ob n γ)
    m n≤m σ

allocᵗ-run : ∀ {Γ A}
  (b : Γ ⊢ BoolVal) (k : Γ V.× Ref ⊢ T .F-ob A)
  n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → Bool) →
  allocᵗ b k .N-ob n γ m n≤m σ ≡
  extendResult A ≤-sucℕ
    (k .N-ob (suc m)
      (Γ .F-hom (≤-trans n≤m ≤-sucℕ) γ , flast {k = m})
      (suc m) ≤-refl (extendStore {n = m} (b .N-ob n γ) σ))
allocᵗ-run {Γ = Γ} {A = A} b k n γ m n≤m σ =
  alloc-run A n (b .N-ob n γ , V.lda k .N-ob n γ) m n≤m σ
  ∙ cong (extendResult A ≤-sucℕ)
      (cong
        (λ q → k .N-ob (suc m)
          (Γ .F-hom q γ , flast {k = m})
          (suc m) ≤-refl (extendStore {n = m} (b .N-ob n γ) σ))
        (isProp≤ _ _))

-- Equality of computations is pointwise equality in the future world, its
-- extension proof, and the input store.
T-ext : ∀ {A n} {t u : T .F-ob A .F-ob n .fst} →
  (∀ m n≤m σ → t m n≤m σ ≡ u m n≤m σ) → t ≡ u
T-ext h = funExt₃ h

{- Reading a location and writing its current value has no effect.

  get i (λ b → set i b t) = t
-}
get-set-currentᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (t : Γ ⊢ T .F-ob A) →
  getᵗ i (setᵗ (V.π₁ V.⋆ i) V.π₂ (V.π₁ V.⋆ t)) ≡ t
get-set-currentᵗ {Γ = Γ} {A = A} i t =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext λ m n≤m σ →
    let
      iₙ = i .N-ob n γ
      γₘ = Γ .F-hom n≤m γ
      iₘ = i .N-ob m γₘ
      wi = weakenRef n≤m iₙ
      i-nat = funExt⁻ (i .N-hom n≤m) γ
      write≡wi = funExt⁻ (Ref .F-id) iₘ ∙ i-nat
      store-path =
        cong (λ r → updateStore {n = m} r
          (lookupStore {n = m} wi σ) σ) write≡wi
        ∙ update-current {n = m} wi σ
    in
    getᵗ-run i (setᵗ (V.π₁ V.⋆ i) V.π₂ (V.π₁ V.⋆ t))
      n γ m n≤m σ
    ∙ setᵗ-run (V.π₁ V.⋆ i) V.π₂ (V.π₁ V.⋆ t)
        m (γₘ , lookupStore {n = m} wi σ) m ≤-refl σ
    ∙ cong (λ τ → t .N-ob m γₘ m ≤-refl τ) store-path
    ∙ cong (λ u → u m ≤-refl σ)
        (funExt⁻ (t .N-hom n≤m) γ)
    ∙ cong (λ q → t .N-ob n γ m q σ) (isProp≤ _ _))

{- Reading immediately after writing returns the written value.

  set i b (get i k) = set i b (k b)
-}
set-get-sameᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b : Γ ⊢ BoolVal)
  (k : Γ V.× BoolVal ⊢ T .F-ob A) →
  setᵗ i b (getᵗ i k) ≡ setᵗ i b ((V.id V.,p b) V.⋆ k)
set-get-sameᵗ {A = A} i b k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext λ m n≤m σ →
    let
      r = weakenRef n≤m (i .N-ob n γ)
      v = b .N-ob n γ
      σ' = updateStore {n = m} r v σ
    in
    setᵗ-run i b (getᵗ i k) n γ m n≤m σ
    ∙ getᵗ-run i k n γ m n≤m σ'
    ∙ cong (λ c → k .N-ob n (γ , c) m n≤m σ')
        (lookup-update-same {n = m} r v σ)
    ∙ sym (setᵗ-run i b ((V.id V.,p b) V.⋆ k)
        n γ m n≤m σ))

{- A later write to the same location overwrites an earlier write.

  set i b (set i c t) = set i c t
-}
set-set-sameᵗ : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b c : Γ ⊢ BoolVal) (t : Γ ⊢ T .F-ob A) →
  setᵗ i b (setᵗ i c t) ≡ setᵗ i c t
set-set-sameᵗ {A = A} i b c t =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext λ m n≤m σ →
    let
      r = weakenRef n≤m (i .N-ob n γ)
      bv = b .N-ob n γ
      cv = c .N-ob n γ
      σ' = updateStore {n = m} r bv σ
    in
    setᵗ-run i b (setᵗ i c t) n γ m n≤m σ
    ∙ setᵗ-run i c t n γ m n≤m σ'
    ∙ cong (t .N-ob n γ m n≤m)
        (update-overwrite {n = m} r bv cv σ)
    ∙ sym (setᵗ-run i c t n γ m n≤m σ))

swapLast : ∀ {Γ A B} → (Γ V.× A) V.× B ⊢ (Γ V.× B) V.× A
swapLast = (((V.π₁ V.⋆ V.π₁) V.,p V.π₂) V.,p (V.π₁ V.⋆ V.π₂))

-- References must be distinct at every stage and environment.  Naturality of
-- references then preserves this condition when the world is extended.
Distinctᵗ : ∀ {Γ} → Γ ⊢ Ref → Γ ⊢ Ref → Type
Distinctᵗ {Γ} i j = ∀ n (γ : Γ .F-ob n .fst) →
  i .N-ob n γ ≡ j .N-ob n γ → ⊥.⊥

{- Reads commute.  No distinctness assumption is required.

  get i (λ b → get j (λ c → k b c))
    = get j (λ c → get i (λ b → k b c))
-}look through Equations Discrete and Base

clean up any unused definitions and imports
get-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref)
  (k : (Γ V.× BoolVal) V.× BoolVal ⊢ T .F-ob A) →
  getᵗ i (getᵗ (V.π₁ V.⋆ j) k) ≡
  getᵗ j (getᵗ (V.π₁ V.⋆ i) (swapLast V.⋆ k))
get-get-commuteᵗ {Γ = Γ} {A = A} i j k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext λ m n≤m σ →
    let
      γₘ = Γ .F-hom n≤m γ
      wi = weakenRef n≤m (i .N-ob n γ)
      wj = weakenRef n≤m (j .N-ob n γ)
      vi = lookupStore {n = m} wi σ
      vj = lookupStore {n = m} wj σ
      iₘ = i .N-ob m γₘ
      jₘ = j .N-ob m γₘ
      ri = weakenRef ≤-refl iₘ
      rj = weakenRef ≤-refl jₘ
      ri≡wi = funExt⁻ (Ref .F-id) iₘ ∙ funExt⁻ (i .N-hom n≤m) γ
      rj≡wj = funExt⁻ (Ref .F-id) jₘ ∙ funExt⁻ (j .N-hom n≤m) γ
    in
    getᵗ-run i (getᵗ (V.π₁ V.⋆ j) k) n γ m n≤m σ
    ∙ getᵗ-run (V.π₁ V.⋆ j) k m (γₘ , vi) m ≤-refl σ
    ∙ cong (λ c → k .N-ob m ((γₘ , vi) , c) m ≤-refl σ)
        (cong σ rj≡wj)
    ∙ sym (cong (λ b → k .N-ob m ((γₘ , b) , vj) m ≤-refl σ)
        (cong σ ri≡wi))
    ∙ sym (getᵗ-run (V.π₁ V.⋆ i) (swapLast V.⋆ k)
        m (γₘ , vj) m ≤-refl σ)
    ∙ sym (getᵗ-run j (getᵗ (V.π₁ V.⋆ i) (swapLast V.⋆ k))
        n γ m n≤m σ))

{- Writes to distinct locations commute.

  set i b (set j c t) = set j c (set i b t)    when i ≢ j
-}
set-set-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref) → Distinctᵗ i j →
  (b c : Γ ⊢ BoolVal) (t : Γ ⊢ T .F-ob A) →
  setᵗ i b (setᵗ j c t) ≡ setᵗ j c (setᵗ i b t)
set-set-commuteᵗ {A = A} i j i≢j b c t =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext λ m n≤m σ →
    let
      wi = weakenRef n≤m (i .N-ob n γ)
      wj = weakenRef n≤m (j .N-ob n γ)
      bv = b .N-ob n γ
      cv = c .N-ob n γ
    in
    setᵗ-run i b (setᵗ j c t) n γ m n≤m σ
    ∙ setᵗ-run j c t n γ m n≤m
        (updateStore {n = m} wi bv σ)
    ∙ cong (t .N-ob n γ m n≤m)
        (update-commute {n = m} wi wj
          (weakenRef-distinct n≤m _ _ (i≢j n γ)) bv cv σ)
    ∙ sym (setᵗ-run i b t n γ m n≤m
        (updateStore {n = m} wj cv σ))
    ∙ sym (setᵗ-run j c (setᵗ i b t) n γ m n≤m σ))

{- A write and a read at distinct locations commute.

  set i b (get j (λ c → k c))
    = get j (λ c → set i b (k c))        when i ≢ j
-}
set-get-commuteᵗ : ∀ {Γ A}
  (i j : Γ ⊢ Ref) → Distinctᵗ i j →
  (b : Γ ⊢ BoolVal) (k : Γ V.× BoolVal ⊢ T .F-ob A) →
  setᵗ i b (getᵗ j k) ≡
  getᵗ j (setᵗ (V.π₁ V.⋆ i) (V.π₁ V.⋆ b) k)
set-get-commuteᵗ {Γ = Γ} {A = A} i j i≢j b k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext λ m n≤m σ →
    let
      γₘ = Γ .F-hom n≤m γ
      wi = weakenRef n≤m (i .N-ob n γ)
      wj = weakenRef n≤m (j .N-ob n γ)
      bv = b .N-ob n γ
      σi = updateStore {n = m} wi bv σ
      vj = lookupStore {n = m} wj σ
      iₘ = i .N-ob m γₘ
      ri = weakenRef ≤-refl iₘ
      bm = b .N-ob m γₘ
      ri≡wi = funExt⁻ (Ref .F-id) iₘ ∙ funExt⁻ (i .N-hom n≤m) γ
      bm≡bv = funExt⁻ (b .N-hom n≤m) γ
      store-right≡left = cong₂
        (λ r v → updateStore {n = m} r v σ) ri≡wi bm≡bv
    in
    setᵗ-run i b (getᵗ j k) n γ m n≤m σ
    ∙ getᵗ-run j k n γ m n≤m σi
    ∙ cong (λ v → k .N-ob m (γₘ , v) m ≤-refl σi)
        (lookup-update-diff {n = m} wi wj
          (weakenRef-distinct n≤m _ _ (i≢j n γ)) bv σ)
    ∙ cong (λ τ → k .N-ob m (γₘ , vj) m ≤-refl τ)
        (sym store-right≡left)
    ∙ sym (setᵗ-run (V.π₁ V.⋆ i) (V.π₁ V.⋆ b) k
        m (γₘ , vj) m ≤-refl σ)
    ∙ sym (getᵗ-run j
        (setᵗ (V.π₁ V.⋆ i) (V.π₁ V.⋆ b) k)
        n γ m n≤m σ))

------------------------------------------------------------------------
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
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext λ m n≤m σ →
    let
      q = ≤-trans n≤m ≤-sucℕ
      γ⁺ = Γ .F-hom q γ
      fresh = flast {k = m}
      c⁺ = c .N-ob (suc m) γ⁺
      cₙ = c .N-ob n γ
      fresh-id = funExt⁻ (Ref .F-id) fresh
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
        (setᵗ-run V.π₂ (V.π₁ V.⋆ c) k
          (suc m) (γ⁺ , fresh) (suc m) ≤-refl
          (extendStore {n = m} (b .N-ob n γ) σ))
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ τ → k .N-ob (suc m) (γ⁺ , fresh)
          (suc m) ≤-refl τ) store-path)
    ∙ sym (allocᵗ-run c k n γ m n≤m σ))

{- Reading the freshly allocated location returns its initial value.

  alloc b (λ i → get i (λ c → k i c))
    = alloc b (λ i → k i b)
-}
alloc-get-freshᵗ : ∀ {Γ A}
  (b : Γ ⊢ BoolVal)
  (k : (Γ V.× Ref) V.× BoolVal ⊢ T .F-ob A) →
  allocᵗ b (getᵗ V.π₂ k) ≡
  allocᵗ b ((V.id V.,p (V.π₁ V.⋆ b)) V.⋆ k)
alloc-get-freshᵗ {Γ = Γ} {A = A} b k =
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext λ m n≤m σ →
    let
      q = ≤-trans n≤m ≤-sucℕ
      γ⁺ = Γ .F-hom q γ
      fresh = flast {k = m}
      bₙ = b .N-ob n γ
      b⁺ = b .N-ob (suc m) γ⁺
      τ = extendStore {n = m} bₙ σ
      fresh-id = funExt⁻ (Ref .F-id) fresh
      b-nat = funExt⁻ (b .N-hom q) γ
      value-path =
        cong (λ r → lookupStore {n = suc m} r τ) fresh-id
        ∙ extendStore-fresh {n = m} bₙ σ
        ∙ sym b-nat
    in
    allocᵗ-run b (getᵗ V.π₂ k) n γ m n≤m σ
    ∙ cong (extendResult A ≤-sucℕ)
        (getᵗ-run V.π₂ k (suc m) (γ⁺ , fresh)
          (suc m) ≤-refl τ)
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ v → k .N-ob (suc m) ((γ⁺ , fresh) , v)
          (suc m) ≤-refl τ) value-path)
    ∙ sym (allocᵗ-run b
        ((V.id V.,p (V.π₁ V.⋆ b)) V.⋆ k)
        n γ m n≤m σ))

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
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext λ m n≤m σ →
    let
      q = ≤-trans n≤m ≤-sucℕ
      γ⁺ = Γ .F-hom q γ
      fresh = flast {k = m}
      wj = weakenRef n≤m (j .N-ob n γ)
      old = weakenRef ≤-sucℕ wj
      j⁺ = j .N-ob (suc m) γ⁺
      rj = weakenRef ≤-refl j⁺
      cₙ = c .N-ob n γ
      c⁺ = c .N-ob (suc m) γ⁺
      σc = updateStore {n = m} wj cₙ σ
      rj≡old =
        funExt⁻ (Ref .F-id) j⁺
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
    allocᵗ-run b
      (setᵗ (V.π₁ V.⋆ j) (V.π₁ V.⋆ c) k)
      n γ m n≤m σ
    ∙ cong (extendResult A ≤-sucℕ)
        (setᵗ-run (V.π₁ V.⋆ j) (V.π₁ V.⋆ c) k
          (suc m) (γ⁺ , fresh) (suc m) ≤-refl
          (extendStore {n = m} (b .N-ob n γ) σ))
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ τ → k .N-ob (suc m) (γ⁺ , fresh)
          (suc m) ≤-refl τ) store-path)
    ∙ sym (allocᵗ-run b k n γ m n≤m σc)
    ∙ sym (setᵗ-run j c (allocᵗ b k) n γ m n≤m σ))

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
  makeNatTransPath (funExt λ n → funExt λ γ → T-ext λ m n≤m σ →
    let
      q = ≤-trans n≤m ≤-sucℕ
      γₘ = Γ .F-hom n≤m γ
      γ⁺ = Γ .F-hom q γ
      γ⁺ʳ = Γ .F-hom ≤-sucℕ γₘ
      fresh = flast {k = m}
      wj = weakenRef n≤m (j .N-ob n γ)
      old = weakenRef ≤-sucℕ wj
      j⁺ = j .N-ob (suc m) γ⁺
      rj = weakenRef ≤-refl j⁺
      bₙ = b .N-ob n γ
      bₘ = b .N-ob m γₘ
      τ = extendStore {n = m} bₙ σ
      vj = lookupStore {n = m} wj σ
      rj≡old =
        funExt⁻ (Ref .F-id) j⁺
        ∙ funExt⁻ (j .N-hom q) γ
        ∙ sym (weakenRef-comp n≤m ≤-sucℕ (j .N-ob n γ))
      value-path =
        cong (λ r → lookupStore {n = suc m} r τ) rj≡old
        ∙ alloc-get-distinct {n = m} wj bₙ σ
      γ-path = funExt⁻ (Γ .F-seq n≤m ≤-sucℕ) γ
      b-path = funExt⁻ (b .N-hom n≤m) γ
      store-path = cong (λ v → extendStore {n = m} v σ) (sym b-path)
    in
    allocᵗ-run b (getᵗ (V.π₁ V.⋆ j) k) n γ m n≤m σ
    ∙ cong (extendResult A ≤-sucℕ)
        (getᵗ-run (V.π₁ V.⋆ j) k
          (suc m) (γ⁺ , fresh) (suc m) ≤-refl τ)
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ v → k .N-ob (suc m) ((γ⁺ , fresh) , v)
          (suc m) ≤-refl τ) value-path)
    ∙ cong (extendResult A ≤-sucℕ)
        (cong₂
          (λ δ υ → k .N-ob (suc m) ((δ , fresh) , vj)
            (suc m) ≤-refl υ)
          γ-path store-path)
    ∙ sym (allocᵗ-run (V.π₁ V.⋆ b) (swapLast V.⋆ k)
        m (γₘ , vj) m ≤-refl σ)
    ∙ sym (getᵗ-run j
        (allocᵗ (V.π₁ V.⋆ b) (swapLast V.⋆ k))
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
