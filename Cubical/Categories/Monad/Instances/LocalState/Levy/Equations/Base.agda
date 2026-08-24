module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base where

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

opaque
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

opaque
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

-- Specialized form used when the allocation continuation pairs the extended
-- context with the value of b.  Naming this reduction avoids depending on
-- unfolding the cartesian structure in downstream equation modules.
allocᵗ-current-run : ∀ {Γ A}
  (b : Γ ⊢ BoolVal)
  (k : (Γ V.× Ref) V.× BoolVal ⊢ T .F-ob A)
  n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → Bool) →
  allocᵗ b ((V.id V.,p (V.π₁ V.⋆ b)) V.⋆ k)
      .N-ob n γ m n≤m σ ≡
  extendResult A ≤-sucℕ
    (k .N-ob (suc m)
      ((Γ .F-hom (≤-trans n≤m ≤-sucℕ) γ , flast {k = m}) ,
       b .N-ob (suc m) (Γ .F-hom (≤-trans n≤m ≤-sucℕ) γ))
      (suc m) ≤-refl (extendStore {n = m} (b .N-ob n γ) σ))
allocᵗ-current-run b k n γ m n≤m σ =
  allocᵗ-run b ((V.id V.,p (V.π₁ V.⋆ b)) V.⋆ k)
    n γ m n≤m σ

setᵗ-current-run : ∀ {Γ A}
  (i : Γ ⊢ Ref) (b : Γ ⊢ BoolVal)
  (k : Γ V.× BoolVal ⊢ T .F-ob A)
  n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → Bool) →
  setᵗ i b ((V.id V.,p b) V.⋆ k) .N-ob n γ m n≤m σ ≡
  k .N-ob n (γ , b .N-ob n γ) m n≤m
    (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
      (b .N-ob n γ) σ)
setᵗ-current-run i b k n γ m n≤m σ =
  setᵗ-run i b ((V.id V.,p b) V.⋆ k) n γ m n≤m σ

swapLast : ∀ {Γ A B} → (Γ V.× A) V.× B ⊢ (Γ V.× B) V.× A
swapLast = (((V.π₁ V.⋆ V.π₁) V.,p V.π₂) V.,p (V.π₁ V.⋆ V.π₂))

-- Equality of computations is pointwise equality in the future world, its
-- extension proof, and the input store.
T-ext : ∀ {A n} {t u : T .F-ob A .F-ob n .fst} →
  (∀ m n≤m σ → t m n≤m σ ≡ u m n≤m σ) → t ≡ u
T-ext h = funExt₃ h

-- References must be distinct at every stage and environment.  Naturality of
-- references then preserves this condition when the world is extended.
Distinctᵗ : ∀ {Γ} → Γ ⊢ Ref → Γ ⊢ Ref → Type
Distinctᵗ {Γ} i j = ∀ n (γ : Γ .F-ob n .fst) →
  i .N-ob n γ ≡ j .N-ob n γ → ⊥.⊥
