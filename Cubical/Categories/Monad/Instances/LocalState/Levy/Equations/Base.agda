open import Cubical.Data.Sigma
open import Cubical.Data.Fin
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order
  using (_≤_ ; ≤-refl ; ≤-trans ; ≤-sucℕ ; isProp≤)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Presheaf.CCC
open import Cubical.Categories.Presheaf.Constructions.Exponential
  using (_⇒PshLarge_)
open import Cubical.Categories.Presheaf.Morphism.Alt

module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base
  (V : hSet ℓ-zero) where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base V
open import Cubical.Categories.Monad.Instances.LocalState.Levy.PiSigma V

open Functor
open NatTrans
open PshHom

------------------------------------------------------------------------
-- Contextual state operations
------------------------------------------------------------------------

Val-CCC : CartesianClosedCategory _ _
Val-CCC = Cubical.Categories.Presheaf.CCC.𝓟-CCC (World ^op) ℓ-zero

module CC = CartesianClosedCategory Val-CCC

-- Terms are natural transformations between value presheaves.  Keeping the
-- context explicit below lets the state operations be used under weakening.
infix 1 _⊢_
_⊢_ : CC.ob → CC.ob → Type _
Γ ⊢ A = CC.C [ Γ , A ]

-- Algebraic operations in an arbitrary context.
getᵗ : ∀ {Γ A} →
  Γ ⊢ Ref →
  Γ CC.× VVal ⊢ T .F-ob A →
  Γ ⊢ T .F-ob A
getᵗ {A = A} i k = (i CC.,p CC.lda k) CC.⋆ get A

setᵗ : ∀ {Γ A} →
  Γ ⊢ Ref →
  Γ ⊢ VVal →
  Γ ⊢ T .F-ob A →
  Γ ⊢ T .F-ob A
setᵗ {A = A} i b t = ((i CC.,p b) CC.,p t) CC.⋆ set A

allocᵗ : ∀ {Γ A} →
  Γ ⊢ VVal →
  Γ CC.× Ref ⊢ T .F-ob A →
  Γ ⊢ T .F-ob A
allocᵗ {A = A} b k = (b CC.,p CC.lda k) CC.⋆ alloc A

------------------------------------------------------------------------
-- Pointwise computation semantics
------------------------------------------------------------------------

-- A computation started in world m may finish in a larger world p.  When the
-- same result is viewed from an earlier world, only its lower-bound witness
-- changes; the final world, value, and store are unchanged.
extendResult : (B : CC.ob) {m p : ℕ} →
  m ≤ p → F .F-ob B .F-ob p .fst → F .F-ob B .F-ob m .fst
extendResult B m≤p (q , p≤q , b , υ) =
  q , ≤-trans m≤p p≤q , b , υ

extendResult-refl : (B : CC.ob) {m : ℕ}
  (r : F .F-ob B .F-ob m .fst) → extendResult B ≤-refl r ≡ r
extendResult-refl B (q , m≤q , b , υ) =
  ΣPathP (refl , ΣPathP (isProp≤ _ _ , ΣPathP (refl , refl)))

-- Pointwise semantics of Kleisli extension: run t, feed its value and final
-- store to k at the world produced by t, then rebase the result to world m.
runBindT : (A B : CC.ob) {n : ℕ} →
  T .F-ob A .F-ob n .fst →
  (A ⇒PshLarge (T .F-ob B)) .F-ob n .fst →
  T .F-ob B .F-ob n .fst
runBindT A B {n} t k m n≤m σ with t m n≤m σ
... | p , m≤p , a , τ =
  extendResult B m≤p
    (k .N-ob p (≤-trans n≤m m≤p , a) p ≤-refl τ)

bindT-run : ∀ (A B : CC.ob) {n : ℕ}
  (t : T .F-ob A .F-ob n .fst)
  (k : (A ⇒PshLarge (T .F-ob B)) .F-ob n .fst)
  (m : ℕ) (n≤m : n ≤ m) (σ : Fin m → V .fst) →
  bindT .N-ob n (t , k) m n≤m σ ≡ runBindT A B t k m n≤m σ
bindT-run A B {n} t k m n≤m σ with t m n≤m σ
... | p , m≤p , a , τ =
  cong (extendResult B m≤p)
    (cong
      (λ h → k .N-ob p (h , a) p ≤-refl τ)
      (isProp≤ _ _))

-- The following three lemmas expose the concrete store semantics hidden by
-- the definitions of the algebraic operations.  Subsequent equations reduce
-- to these rules plus the lookup/update laws from Levy.Base.
get-run : ∀ (A : CC.ob) n
  (x : (Ref CC.× (VVal CC.⇒ (T .F-ob A))) .F-ob n .fst)
  m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
  get A .N-ob n x m n≤m σ ≡
  x .snd .N-ob m
    (n≤m , lookupStore {n = m} (weakenRef n≤m (x .fst)) σ)
    m ≤-refl σ
get-run A n (i , k) m n≤m σ =
  bindT-run VVal A
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

ignoreUnit : (A : CC.ob) → (T .F-ob A) ⊢ (UnitVal CC.⇒ (T .F-ob A))
ignoreUnit A = CC.lda CC.π₁

set-run : ∀ (A : CC.ob) n
  (x : ((Ref CC.× VVal) CC.× (T .F-ob A)) .F-ob n .fst)
  m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
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

alloc-run : ∀ (A : CC.ob) n
  (x : (VVal CC.× (Ref CC.⇒ (T .F-ob A))) .F-ob n .fst)
  m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
  alloc A .N-ob n x m n≤m σ ≡
  extendResult A ≤-sucℕ
    (x .snd .N-ob (suc m)
      (≤-trans n≤m ≤-sucℕ , flast {k = m})
      (suc m) ≤-refl (extendStore {n = m} (x .fst) σ))
alloc-run A n (b , k) m n≤m σ =
  bindT-run Ref A (allocM .N-ob n b) k m n≤m σ

------------------------------------------------------------------------
-- Contextual operation runners
------------------------------------------------------------------------

opaque
  getᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (k : Γ CC.× VVal ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    getᵗ i k .N-ob n γ m n≤m σ ≡
    k .N-ob m
      (Γ .F-hom n≤m γ ,
       lookupStore {n = m} (weakenRef n≤m (i .N-ob n γ)) σ)
      m ≤-refl σ
  getᵗ-run {Γ = Γ} {A = A} i k n γ m n≤m σ =
    get-run A n (i .N-ob n γ , CC.lda k .N-ob n γ) m n≤m σ
    ∙ cong
        (λ q → k .N-ob m
          (Γ .F-hom q γ ,
           lookupStore {n = m} (weakenRef n≤m (i .N-ob n γ)) σ)
          m ≤-refl σ)
        (isProp≤ _ _)

opaque
  setᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (b : Γ ⊢ VVal) (t : Γ ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    setᵗ i b t .N-ob n γ m n≤m σ ≡
    t .N-ob n γ m n≤m
      (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
        (b .N-ob n γ) σ)
  setᵗ-run {A = A} i b t n γ m n≤m σ =
    set-run A n ((i .N-ob n γ , b .N-ob n γ) , t .N-ob n γ)
      m n≤m σ

allocᵗ-run : ∀ {Γ A}
  (b : Γ ⊢ VVal) (k : Γ CC.× Ref ⊢ T .F-ob A)
  n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
  allocᵗ b k .N-ob n γ m n≤m σ ≡
  extendResult A ≤-sucℕ
    (k .N-ob (suc m)
      (Γ .F-hom (≤-trans n≤m ≤-sucℕ) γ , flast {k = m})
      (suc m) ≤-refl (extendStore {n = m} (b .N-ob n γ) σ))
allocᵗ-run {Γ = Γ} {A = A} b k n γ m n≤m σ =
  alloc-run A n (b .N-ob n γ , CC.lda k .N-ob n γ) m n≤m σ
  ∙ cong (extendResult A ≤-sucℕ)
      (cong
        (λ q → k .N-ob (suc m)
          (Γ .F-hom q γ , flast {k = m})
          (suc m) ≤-refl (extendStore {n = m} (b .N-ob n γ) σ))
        (isProp≤ _ _))

------------------------------------------------------------------------
-- Specialized runners and context rearrangement
------------------------------------------------------------------------

-- These small opaque terms are deliberate elaboration boundaries.  Expanding
-- their CCC pairings in law endpoints makes Agda normalize very large terms.
opaque
  -- Substitution of a value into a continuation is kept opaque because the
  -- expanded CCC pairing is expensive in equality endpoints for abstract V.
  value-contᵗ : ∀ {Γ A} →
    (b : Γ ⊢ VVal) (k : Γ CC.× VVal ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  value-contᵗ b k = (CC.id CC.,p b) CC.⋆ k

  value-contᵗ-run : ∀ {Γ A}
    (b : Γ ⊢ VVal) (k : Γ CC.× VVal ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    value-contᵗ b k .N-ob n γ m n≤m σ ≡
    k .N-ob n (γ , b .N-ob n γ) m n≤m σ
  value-contᵗ-run b k n γ m n≤m σ = refl

  set-currentᵗ : ∀ {Γ A} →
    (i : Γ ⊢ Ref) (b : Γ ⊢ VVal)
    (k : Γ CC.× VVal ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  set-currentᵗ i b k = setᵗ i b (value-contᵗ b k)

  set-currentᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (b : Γ ⊢ VVal)
    (k : Γ CC.× VVal ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-currentᵗ i b k .N-ob n γ m n≤m σ ≡
    k .N-ob n (γ , b .N-ob n γ) m n≤m
      (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
        (b .N-ob n γ) σ)
  set-currentᵗ-run i b k n γ m n≤m σ =
    setᵗ-run i b (value-contᵗ b k) n γ m n≤m σ
    ∙ value-contᵗ-run b k n γ m n≤m
        (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
          (b .N-ob n γ) σ)

opaque
  set-get-same-lhsᵗ : ∀ {Γ A} →
    (i : Γ ⊢ Ref) (b : Γ ⊢ VVal)
    (k : Γ CC.× VVal ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  set-get-same-lhsᵗ i b k = setᵗ i b (getᵗ i k)

  set-get-same-lhsᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (b : Γ ⊢ VVal)
    (k : Γ CC.× VVal ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-get-same-lhsᵗ i b k .N-ob n γ m n≤m σ ≡
    k .N-ob n (γ , b .N-ob n γ) m n≤m
      (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
        (b .N-ob n γ) σ)
  set-get-same-lhsᵗ-run {Γ = Γ} i b k n γ m n≤m σ =
    let
      σ' : Fin m → V .fst
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

opaque
  set-set-same-lhsᵗ : ∀ {Γ A} →
    (i : Γ ⊢ Ref) (b c : Γ ⊢ VVal) (t : Γ ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  set-set-same-lhsᵗ i b c t = setᵗ i b (setᵗ i c t)

  set-set-same-lhsᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (b c : Γ ⊢ VVal) (t : Γ ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-set-same-lhsᵗ i b c t .N-ob n γ m n≤m σ ≡
    t .N-ob n γ m n≤m
      (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
        (c .N-ob n γ)
        (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
          (b .N-ob n γ) σ))
  set-set-same-lhsᵗ-run {A = A} i b c t n γ m n≤m σ =
    setᵗ-run {A = A} i b (setᵗ i c t) n γ m n≤m σ
    ∙ setᵗ-run {A = A} i c t n γ m n≤m
        (updateStore {n = m}
          (weakenRef n≤m (i .N-ob n γ)) (b .N-ob n γ) σ)

opaque
  set-set-commute-lhsᵗ : ∀ {Γ A} →
    (i j : Γ ⊢ Ref) (b c : Γ ⊢ VVal) (t : Γ ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  set-set-commute-lhsᵗ i j b c t = setᵗ i b (setᵗ j c t)

  set-set-commute-lhsᵗ-run : ∀ {Γ A}
    (i j : Γ ⊢ Ref) (b c : Γ ⊢ VVal) (t : Γ ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-set-commute-lhsᵗ i j b c t .N-ob n γ m n≤m σ ≡
    t .N-ob n γ m n≤m
      (updateStore {n = m} (weakenRef n≤m (j .N-ob n γ))
        (c .N-ob n γ)
        (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
          (b .N-ob n γ) σ))
  set-set-commute-lhsᵗ-run {A = A} i j b c t n γ m n≤m σ =
    setᵗ-run {A = A} i b (setᵗ j c t) n γ m n≤m σ
    ∙ setᵗ-run {A = A} j c t n γ m n≤m
        (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
          (b .N-ob n γ) σ)

  set-set-commute-rhsᵗ : ∀ {Γ A} →
    (i j : Γ ⊢ Ref) (b c : Γ ⊢ VVal) (t : Γ ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  set-set-commute-rhsᵗ i j b c t = setᵗ j c (setᵗ i b t)

  set-set-commute-rhsᵗ-run : ∀ {Γ A}
    (i j : Γ ⊢ Ref) (b c : Γ ⊢ VVal) (t : Γ ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-set-commute-rhsᵗ i j b c t .N-ob n γ m n≤m σ ≡
    t .N-ob n γ m n≤m
      (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
        (b .N-ob n γ)
        (updateStore {n = m} (weakenRef n≤m (j .N-ob n γ))
          (c .N-ob n γ) σ))
  set-set-commute-rhsᵗ-run {A = A} i j b c t n γ m n≤m σ =
    setᵗ-run {A = A} j c (setᵗ i b t) n γ m n≤m σ
    ∙ setᵗ-run {A = A} i b t n γ m n≤m
        (updateStore {n = m} (weakenRef n≤m (j .N-ob n γ))
          (c .N-ob n γ) σ)

swapLast : ∀ {Γ A B} → (Γ CC.× A) CC.× B ⊢ (Γ CC.× B) CC.× A
swapLast = (((CC.π₁ CC.⋆ CC.π₁) CC.,p CC.π₂) CC.,p (CC.π₁ CC.⋆ CC.π₂))

------------------------------------------------------------------------
-- Opaque get and set continuations
------------------------------------------------------------------------

opaque
  -- Naming this CCC composite is a type-checking boundary.  Expanding it in
  -- downstream runner endpoints otherwise normalizes the full product/lambda
  -- term during conversion.
  set-current-contᵗ : ∀ {Γ A} →
    (i : Γ ⊢ Ref) (t : Γ ⊢ T .F-ob A) →
    Γ CC.× VVal ⊢ T .F-ob A
  set-current-contᵗ i t =
    setᵗ (CC.π₁ CC.⋆ i) CC.π₂ (CC.π₁ CC.⋆ t)

  set-current-contᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (t : Γ ⊢ T .F-ob A)
    n (γ : (Γ CC.× VVal) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-current-contᵗ i t .N-ob n γ m n≤m σ ≡
    t .N-ob n (γ .fst) m n≤m
      (updateStore {n = m}
        (weakenRef {n = n} {m = m} n≤m (i .N-ob n (γ .fst)))
        (γ .snd) σ)
  set-current-contᵗ-run {A = A} i t n γ m n≤m σ =
    setᵗ-run {A = A} (CC.π₁ CC.⋆ i) CC.π₂ (CC.π₁ CC.⋆ t)
      n γ m n≤m σ

opaque
  get-set-current-store : ∀ {Γ n m}
    (i : Γ ⊢ Ref) (γ : Γ .F-ob n .fst)
    (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    updateStore {n = m}
      (weakenRef {n = m} {m = m} ≤-refl
        (i .N-ob m (Γ .F-hom n≤m γ)))
      (lookupStore {n = m}
        (weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)) σ)
      σ ≡ σ
  get-set-current-store {Γ = Γ} {n = n} {m = m} i γ n≤m σ =
    let
      wi = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
      write≡wi =
        funExt⁻ (Ref .F-id {x = m})
          (i .N-ob m (Γ .F-hom n≤m γ))
        ∙ funExt⁻ (i .N-hom n≤m) γ
    in
    cong (λ r → updateStore {n = m} r
      (lookupStore {n = m} wi σ) σ) write≡wi
    ∙ update-current {n = m} wi σ

opaque
  get-set-current-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (t : Γ ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
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

opaque
  set-read-contᵗ : ∀ {Γ A} →
    (i : Γ ⊢ Ref) (b : Γ ⊢ VVal)
    (k : Γ CC.× VVal ⊢ T .F-ob A) →
    Γ CC.× VVal ⊢ T .F-ob A
  set-read-contᵗ i b k =
    setᵗ (CC.π₁ CC.⋆ i) (CC.π₁ CC.⋆ b) k

  set-read-contᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref) (b : Γ ⊢ VVal)
    (k : Γ CC.× VVal ⊢ T .F-ob A)
    n (δ : (Γ CC.× VVal) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-read-contᵗ i b k .N-ob n δ m n≤m σ ≡
    k .N-ob n δ m n≤m
      (updateStore {n = m}
        (weakenRef n≤m (i .N-ob n (δ .fst)))
        (b .N-ob n (δ .fst)) σ)
  set-read-contᵗ-run {A = A} i b k n δ m n≤m σ =
    setᵗ-run {A = A} (CC.π₁ CC.⋆ i) (CC.π₁ CC.⋆ b) k
      n δ m n≤m σ

opaque
  set-get-commute-lhsᵗ : ∀ {Γ A} →
    (i j : Γ ⊢ Ref) (b : Γ ⊢ VVal)
    (k : Γ CC.× VVal ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  set-get-commute-lhsᵗ i j b k = setᵗ i b (getᵗ j k)

  set-get-commute-lhsᵗ-run : ∀ {Γ A}
    (i j : Γ ⊢ Ref) (b : Γ ⊢ VVal)
    (k : Γ CC.× VVal ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-get-commute-lhsᵗ i j b k .N-ob n γ m n≤m σ ≡
    k .N-ob m
      (Γ .F-hom n≤m γ ,
       lookupStore {n = m}
         (weakenRef n≤m (j .N-ob n γ))
         (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
           (b .N-ob n γ) σ))
      m ≤-refl
      (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
        (b .N-ob n γ) σ)
  set-get-commute-lhsᵗ-run {A = A} i j b k n γ m n≤m σ =
    setᵗ-run {A = A} i b (getᵗ j k) n γ m n≤m σ
    ∙ getᵗ-run {A = A} j k n γ m n≤m
        (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
          (b .N-ob n γ) σ)

  set-get-commute-rhsᵗ : ∀ {Γ A} →
    (i j : Γ ⊢ Ref) (b : Γ ⊢ VVal)
    (k : Γ CC.× VVal ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  set-get-commute-rhsᵗ i j b k = getᵗ j (set-read-contᵗ i b k)

  set-get-commute-rhsᵗ-run : ∀ {Γ A}
    (i j : Γ ⊢ Ref) (b : Γ ⊢ VVal)
    (k : Γ CC.× VVal ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-get-commute-rhsᵗ i j b k .N-ob n γ m n≤m σ ≡
    k .N-ob m
      (Γ .F-hom n≤m γ ,
       lookupStore {n = m} (weakenRef n≤m (j .N-ob n γ)) σ)
      m ≤-refl
      (updateStore {n = m}
        (weakenRef {n = m} {m = m} ≤-refl
          (i .N-ob m (Γ .F-hom n≤m γ)))
        (b .N-ob m (Γ .F-hom n≤m γ)) σ)
  set-get-commute-rhsᵗ-run {Γ = Γ} {A = A} i j b k n γ m n≤m σ =
    let
      γₘ : Γ .F-ob m .fst
      γₘ = Γ .F-hom n≤m γ
      vj : V .fst
      vj = lookupStore {n = m} (weakenRef n≤m (j .N-ob n γ)) σ
    in
    getᵗ-run {A = A} j (set-read-contᵗ i b k) n γ m n≤m σ
    ∙ set-read-contᵗ-run i b k m (γₘ , vj) m ≤-refl σ

opaque
  -- Keep the lifted inner read out of the exported equality endpoint's
  -- conversion problem.
  left-read-contᵗ : ∀ {Γ A} →
    (j : Γ ⊢ Ref)
    (k : (Γ CC.× VVal) CC.× VVal ⊢ T .F-ob A) →
    Γ CC.× VVal ⊢ T .F-ob A
  left-read-contᵗ {Γ = Γ} j k =
    getᵗ (CC.π₁ {a = Γ} {b = VVal} CC.⋆ j) k

  left-read-contᵗ-run : ∀ {Γ A}
    (j : Γ ⊢ Ref)
    (k : (Γ CC.× VVal) CC.× VVal ⊢ T .F-ob A)
    n (δ : (Γ CC.× VVal) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    left-read-contᵗ j k .N-ob n δ m n≤m σ ≡
    k .N-ob m
      ((Γ CC.× VVal) .F-hom n≤m δ ,
       lookupStore {n = m}
         (weakenRef {n = n} {m = m} n≤m
           ((CC.π₁ {a = Γ} {b = VVal} CC.⋆ j) .N-ob n δ)) σ)
      m ≤-refl σ
  left-read-contᵗ-run {Γ = Γ} {A = A} j k n δ m n≤m σ =
    getᵗ-run {Γ = Γ CC.× VVal} {A = A}
      (CC.π₁ {a = Γ} {b = VVal} CC.⋆ j) k n δ m n≤m σ

opaque
  right-read-contᵗ : ∀ {Γ A} →
    (i : Γ ⊢ Ref)
    (k : (Γ CC.× VVal) CC.× VVal ⊢ T .F-ob A) →
    Γ CC.× VVal ⊢ T .F-ob A
  right-read-contᵗ {Γ = Γ} i k =
    getᵗ (CC.π₁ {a = Γ} {b = VVal} CC.⋆ i) (swapLast CC.⋆ k)

  right-read-contᵗ-run : ∀ {Γ A}
    (i : Γ ⊢ Ref)
    (k : (Γ CC.× VVal) CC.× VVal ⊢ T .F-ob A)
    n (δ : (Γ CC.× VVal) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    right-read-contᵗ i k .N-ob n δ m n≤m σ ≡
    (swapLast CC.⋆ k) .N-ob m
      ((Γ CC.× VVal) .F-hom n≤m δ ,
       lookupStore {n = m}
         (weakenRef {n = n} {m = m} n≤m
           ((CC.π₁ {a = Γ} {b = VVal} CC.⋆ i) .N-ob n δ)) σ)
      m ≤-refl σ
  right-read-contᵗ-run {Γ = Γ} {A = A} i k n δ m n≤m σ =
    getᵗ-run {Γ = Γ CC.× VVal} {A = A}
      (CC.π₁ {a = Γ} {b = VVal} CC.⋆ i) (swapLast CC.⋆ k)
      n δ m n≤m σ

------------------------------------------------------------------------
-- Opaque allocation continuations
------------------------------------------------------------------------

opaque
  set-fresh-contᵗ : ∀ {Γ A} →
    (c : Γ ⊢ VVal) (k : Γ CC.× Ref ⊢ T .F-ob A) →
    Γ CC.× Ref ⊢ T .F-ob A
  set-fresh-contᵗ {Γ = Γ} c k =
    setᵗ (CC.π₂ {a = Γ} {b = Ref})
      (CC.π₁ {a = Γ} {b = Ref} CC.⋆ c) k

  set-fresh-contᵗ-run : ∀ {Γ A}
    (c : Γ ⊢ VVal) (k : Γ CC.× Ref ⊢ T .F-ob A)
    n (δ : (Γ CC.× Ref) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-fresh-contᵗ c k .N-ob n δ m n≤m σ ≡
    k .N-ob n δ m n≤m
      (updateStore {n = m}
        (weakenRef n≤m ((CC.π₂ {a = Γ} {b = Ref}) .N-ob n δ))
        ((CC.π₁ {a = Γ} {b = Ref} CC.⋆ c) .N-ob n δ) σ)
  set-fresh-contᵗ-run {Γ = Γ} {A = A} c k n δ m n≤m σ =
    setᵗ-run {A = A} (CC.π₂ {a = Γ} {b = Ref})
      (CC.π₁ {a = Γ} {b = Ref} CC.⋆ c) k n δ m n≤m σ

opaque
  get-fresh-contᵗ : ∀ {Γ A} →
    (k : (Γ CC.× Ref) CC.× VVal ⊢ T .F-ob A) →
    Γ CC.× Ref ⊢ T .F-ob A
  get-fresh-contᵗ {Γ = Γ} k =
    getᵗ (CC.π₂ {a = Γ} {b = Ref}) k

  get-fresh-contᵗ-run : ∀ {Γ A}
    (k : (Γ CC.× Ref) CC.× VVal ⊢ T .F-ob A)
    n (δ : (Γ CC.× Ref) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    get-fresh-contᵗ k .N-ob n δ m n≤m σ ≡
    k .N-ob m
      ((Γ CC.× Ref) .F-hom n≤m δ ,
       lookupStore {n = m}
         (weakenRef n≤m ((CC.π₂ {a = Γ} {b = Ref}) .N-ob n δ)) σ)
      m ≤-refl σ
  get-fresh-contᵗ-run {Γ = Γ} {A = A} k n δ m n≤m σ =
    getᵗ-run {A = A} (CC.π₂ {a = Γ} {b = Ref}) k n δ m n≤m σ

opaque
  alloc-currentᵗ : ∀ {Γ A} →
    (b : Γ ⊢ VVal)
    (k : (Γ CC.× Ref) CC.× VVal ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  alloc-currentᵗ b k =
    allocᵗ b ((CC.id CC.,p (CC.π₁ CC.⋆ b)) CC.⋆ k)

  alloc-currentᵗ-run : ∀ {Γ A}
    (b : Γ ⊢ VVal)
    (k : (Γ CC.× Ref) CC.× VVal ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    alloc-currentᵗ b k .N-ob n γ m n≤m σ ≡
    extendResult A ≤-sucℕ
      (k .N-ob (suc m)
        ((Γ .F-hom (≤-trans n≤m ≤-sucℕ) γ , flast {k = m}) ,
         b .N-ob (suc m) (Γ .F-hom (≤-trans n≤m ≤-sucℕ) γ))
        (suc m) ≤-refl (extendStore {n = m} (b .N-ob n γ) σ))
  alloc-currentᵗ-run b k n γ m n≤m σ =
    allocᵗ-run b ((CC.id CC.,p (CC.π₁ CC.⋆ b)) CC.⋆ k)
      n γ m n≤m σ

opaque
  set-old-contᵗ : ∀ {Γ A} →
    (j : Γ ⊢ Ref) (c : Γ ⊢ VVal)
    (k : Γ CC.× Ref ⊢ T .F-ob A) →
    Γ CC.× Ref ⊢ T .F-ob A
  set-old-contᵗ j c k =
    setᵗ (CC.π₁ CC.⋆ j) (CC.π₁ CC.⋆ c) k

  set-old-contᵗ-run : ∀ {Γ A}
    (j : Γ ⊢ Ref) (c : Γ ⊢ VVal)
    (k : Γ CC.× Ref ⊢ T .F-ob A)
    n (δ : (Γ CC.× Ref) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    set-old-contᵗ j c k .N-ob n δ m n≤m σ ≡
    k .N-ob n δ m n≤m
      (updateStore {n = m}
        (weakenRef n≤m (j .N-ob n (δ .fst)))
        (c .N-ob n (δ .fst)) σ)
  set-old-contᵗ-run {A = A} j c k n δ m n≤m σ =
    setᵗ-run {A = A} (CC.π₁ CC.⋆ j) (CC.π₁ CC.⋆ c) k
      n δ m n≤m σ

opaque
  get-old-contᵗ : ∀ {Γ A} →
    (j : Γ ⊢ Ref)
    (k : (Γ CC.× Ref) CC.× VVal ⊢ T .F-ob A) →
    Γ CC.× Ref ⊢ T .F-ob A
  get-old-contᵗ {Γ = Γ} j k =
    getᵗ (CC.π₁ {a = Γ} {b = Ref} CC.⋆ j) k

  get-old-contᵗ-run : ∀ {Γ A}
    (j : Γ ⊢ Ref)
    (k : (Γ CC.× Ref) CC.× VVal ⊢ T .F-ob A)
    n (δ : (Γ CC.× Ref) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    get-old-contᵗ j k .N-ob n δ m n≤m σ ≡
    k .N-ob m
      ((Γ CC.× Ref) .F-hom n≤m δ ,
       lookupStore {n = m}
         (weakenRef n≤m
           ((CC.π₁ {a = Γ} {b = Ref} CC.⋆ j) .N-ob n δ)) σ)
      m ≤-refl σ
  get-old-contᵗ-run {Γ = Γ} {A = A} j k n δ m n≤m σ =
    getᵗ-run {A = A} (CC.π₁ {a = Γ} {b = Ref} CC.⋆ j) k
      n δ m n≤m σ

opaque
  alloc-old-contᵗ : ∀ {Γ A} →
    (b : Γ ⊢ VVal)
    (k : (Γ CC.× Ref) CC.× VVal ⊢ T .F-ob A) →
    Γ CC.× VVal ⊢ T .F-ob A
  alloc-old-contᵗ {Γ = Γ} b k =
    allocᵗ (CC.π₁ {a = Γ} {b = VVal} CC.⋆ b)
      (swapLast {Γ = Γ} {A = VVal} {B = Ref} CC.⋆ k)

  alloc-old-contᵗ-run : ∀ {Γ A}
    (b : Γ ⊢ VVal)
    (k : (Γ CC.× Ref) CC.× VVal ⊢ T .F-ob A)
    n (δ : (Γ CC.× VVal) .F-ob n .fst)
    m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    alloc-old-contᵗ b k .N-ob n δ m n≤m σ ≡
    extendResult A ≤-sucℕ
      ((swapLast {Γ = Γ} {A = VVal} {B = Ref} CC.⋆ k)
        .N-ob (suc m)
        ((Γ CC.× VVal) .F-hom (≤-trans n≤m ≤-sucℕ) δ ,
         flast {k = m})
        (suc m) ≤-refl
        (extendStore {n = m}
          ((CC.π₁ {a = Γ} {b = VVal} CC.⋆ b) .N-ob n δ) σ))
  alloc-old-contᵗ-run {Γ = Γ} {A = A} b k n δ m n≤m σ =
    allocᵗ-run {A = A} (CC.π₁ {a = Γ} {b = VVal} CC.⋆ b)
      (swapLast {Γ = Γ} {A = VVal} {B = Ref} CC.⋆ k)
      n δ m n≤m σ

opaque
  alloc-get-fresh-lhsᵗ : ∀ {Γ A} →
    (b : Γ ⊢ VVal)
    (k : (Γ CC.× Ref) CC.× VVal ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  alloc-get-fresh-lhsᵗ b k = allocᵗ b (get-fresh-contᵗ k)

  alloc-get-freshᵗ-run : ∀ {Γ A}
    (b : Γ ⊢ VVal)
    (k : (Γ CC.× Ref) CC.× VVal ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    alloc-get-fresh-lhsᵗ b k .N-ob n γ m n≤m σ ≡
    alloc-currentᵗ b k .N-ob n γ m n≤m σ
  alloc-get-freshᵗ-run {Γ = Γ} {A = A} b k n γ m n≤m σ =
    let
      q : n ≤ suc m
      q = ≤-trans n≤m ≤-sucℕ
      γ⁺ = Γ .F-hom q γ
      fresh : Fin (suc m)
      fresh = flast {k = m}
      bₙ = b .N-ob n γ
      τ = extendStore {n = m} bₙ σ
      value-path =
        cong (λ r → lookupStore {n = suc m} r τ)
          (funExt⁻ (Ref .F-id {x = suc m}) fresh)
        ∙ extendStore-fresh {n = m} bₙ σ
        ∙ sym (funExt⁻ (b .N-hom q) γ)
    in
    allocᵗ-run b (get-fresh-contᵗ k) n γ m n≤m σ
    ∙ cong (extendResult A ≤-sucℕ)
        (get-fresh-contᵗ-run {Γ = Γ} {A = A} k
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
    ∙ sym (alloc-currentᵗ-run b k n γ m n≤m σ)

  alloc-set-old-lhsᵗ : ∀ {Γ A} →
    (j : Γ ⊢ Ref) (b c : Γ ⊢ VVal)
    (k : Γ CC.× Ref ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  alloc-set-old-lhsᵗ j b c k = allocᵗ b (set-old-contᵗ j c k)

  alloc-set-old-rhsᵗ : ∀ {Γ A} →
    (j : Γ ⊢ Ref) (b c : Γ ⊢ VVal)
    (k : Γ CC.× Ref ⊢ T .F-ob A) →
    Γ ⊢ T .F-ob A
  alloc-set-old-rhsᵗ j b c k = setᵗ j c (allocᵗ b k)

  alloc-set-oldᵗ-run : ∀ {Γ A}
    (j : Γ ⊢ Ref) (b c : Γ ⊢ VVal)
    (k : Γ CC.× Ref ⊢ T .F-ob A)
    n (γ : Γ .F-ob n .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    alloc-set-old-lhsᵗ j b c k .N-ob n γ m n≤m σ ≡
    alloc-set-old-rhsᵗ j b c k .N-ob n γ m n≤m σ
  alloc-set-oldᵗ-run {Γ = Γ} {A = A} j b c k n γ m n≤m σ =
    let
      q : n ≤ suc m
      q = ≤-trans n≤m ≤-sucℕ
      γ⁺ : Γ .F-ob (suc m) .fst
      γ⁺ = Γ .F-hom q γ
      fresh : Fin (suc m)
      fresh = flast {k = m}
      wj : Fin m
      wj = weakenRef {n = n} {m = m} n≤m (j .N-ob n γ)
      cₙ : V .fst
      cₙ = c .N-ob n γ
      c⁺ : V .fst
      c⁺ = c .N-ob (suc m) γ⁺
      σc : Fin m → V .fst
      σc = updateStore {n = m} wj cₙ σ
      rj≡old =
        funExt⁻ (Ref .F-id {x = suc m}) (j .N-ob (suc m) γ⁺)
        ∙ funExt⁻ (j .N-hom q) γ
        ∙ sym (weakenRef-comp n≤m ≤-sucℕ (j .N-ob n γ))
      store-path =
        cong₂
          (λ r v → updateStore {n = suc m} r v
            (extendStore {n = m} (b .N-ob n γ) σ))
          rj≡old (funExt⁻ (c .N-hom q) γ)
        ∙ update-extendStore-old {n = m} wj (b .N-ob n γ) cₙ σ
    in
    allocᵗ-run {A = A} b (set-old-contᵗ j c k) n γ m n≤m σ
    ∙ cong (extendResult A ≤-sucℕ)
        (set-old-contᵗ-run {Γ = Γ} {A = A} j c k
          (suc m) (γ⁺ , fresh) (suc m) ≤-refl
          (extendStore {n = m} (b .N-ob n γ) σ))
    ∙ cong (extendResult A ≤-sucℕ)
        (cong (λ τ → k .N-ob (suc m) (γ⁺ , fresh)
          (suc m) ≤-refl τ) store-path)
    ∙ sym (allocᵗ-run {A = A} b k n γ m n≤m σc)
    ∙ sym (setᵗ-run {A = A} j c (allocᵗ b k) n γ m n≤m σ)

------------------------------------------------------------------------
-- Distinct references
------------------------------------------------------------------------

-- References must be distinct at every stage and environment.  Naturality of
-- references then preserves this condition when the world is extended.
Distinctᵗ : ∀ {Γ} → Γ ⊢ Ref → Γ ⊢ Ref → Type
Distinctᵗ {Γ} i j = ∀ n (γ : Γ .F-ob n .fst) →
  i .N-ob n γ ≡ j .N-ob n γ → ⊥.⊥
