open import Cubical.Data.Sigma
open import Cubical.Data.Fin
  using (Fin ; discreteFin ; elimFin ; flast ; injectSuc)
open import Cubical.Data.Fin.Properties using (elimFinβ ; inject<-ne)
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order
  using (_≤_ ; ≤-refl ; ≤-trans ; ≤-sucℕ ; isProp≤)
open import Cubical.Data.Nat.Order.Inductive using (isProp<ᵗ)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet)
open import Cubical.Relation.Nullary using (Dec ; decRec ; yes ; no)
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.CartesianClosed.Base
import Cubical.Categories.Presheaf.CCC
open import Cubical.Categories.Presheaf.Constructions.Exponential
  using (_⇒PshLarge_)
open import Cubical.Categories.Presheaf.Morphism.Alt

module Cubical.Categories.Monad.Instances.LocalState.Levy.Equations.Base
  (V : hSet ℓ-zero) where

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base V

open Functor
open NatTrans
open PshHom

-- The categorical definitions of getᵗ, setᵗ, and allocᵗ expand through
-- products, exponentials, and the presheaf local-state monad. If downstream
-- equation proofs unfold them, Agda repeatedly normalizes these large terms
-- during conversion checking. We therefore make the operations opaque and
-- expose their pointwise β-rules as the computational interface. Each body
-- and β-rule is checked here, with explicit unfolding enabled only while the
-- β-rules are proved. Opacity changes only definitional reduction outside
-- those proofs.

------------------------------------------------------------------------
-- Contextual terms
------------------------------------------------------------------------

Val-CCC : CartesianClosedCategory _ _
Val-CCC = Cubical.Categories.Presheaf.CCC.𝓟-CCC (World ^op) ℓ-zero

module CC = CartesianClosedCategory Val-CCC

infix 1 _⊢_
_⊢_ : CC.ob → CC.ob → Type _
Γ ⊢ A = CC.C [ Γ , A ]

infixl 8 _[_]ᵗ

wkᵗ : ∀ {Γ A B} → Γ ⊢ A → Γ CC.× B ⊢ A
wkᵗ f = CC.π₁ CC.⋆ f

varᵗ : ∀ {Γ A} → Γ CC.× A ⊢ A
varᵗ = CC.π₂

_[_]ᵗ : ∀ {Γ A B} → Γ CC.× A ⊢ B → Γ ⊢ A → Γ ⊢ B
k [ a ]ᵗ = (CC.id CC.,p a) CC.⋆ k

swapLast : ∀ {Γ A B} → (Γ CC.× A) CC.× B ⊢ (Γ CC.× B) CC.× A
swapLast =
  (((CC.π₁ CC.⋆ CC.π₁) CC.,p CC.π₂) CC.,p (CC.π₁ CC.⋆ CC.π₂))

exchangeᵗ : ∀ {Γ A B C} → (Γ CC.× A) CC.× B ⊢ C →
  (Γ CC.× B) CC.× A ⊢ C
exchangeᵗ k = swapLast CC.⋆ k

-- References are distinct at every world and environment.
Distinctᵗ : ∀ {Γ} → Γ ⊢ Ref → Γ ⊢ Ref → Type
Distinctᵗ {Γ} i j = ∀ n (γ : (Γ ⟅ n ⟆) .fst) →
  i .N-ob n γ ≡ j .N-ob n γ → ⊥.⊥

------------------------------------------------------------------------
-- Contextual state operations
------------------------------------------------------------------------

opaque
  getᵗ : ∀ {Γ A} →
    Γ ⊢ Ref →
    Γ CC.× VVal ⊢ T ⟅ A ⟆ →
    Γ ⊢ T ⟅ A ⟆
  getᵗ {A = A} i k = (i CC.,p CC.lda k) CC.⋆ get A

  setᵗ : ∀ {Γ A} →
    Γ ⊢ Ref →
    Γ ⊢ VVal →
    Γ ⊢ T ⟅ A ⟆ →
    Γ ⊢ T ⟅ A ⟆
  setᵗ {A = A} i b t = ((i CC.,p b) CC.,p t) CC.⋆ set A

  allocᵗ : ∀ {Γ A} →
    Γ ⊢ VVal →
    Γ CC.× Ref ⊢ T ⟅ A ⟆ →
    Γ ⊢ T ⟅ A ⟆
  allocᵗ {A = A} b k = (b CC.,p CC.lda k) CC.⋆ alloc A

------------------------------------------------------------------------
-- Computation support
------------------------------------------------------------------------

extendResult : (B : CC.ob) {m p : ℕ} →
  m ≤ p → ((F ⟅ B ⟆) ⟅ p ⟆) .fst → ((F ⟅ B ⟆) ⟅ m ⟆) .fst
extendResult B m≤p (q , p≤q , b , υ) =
  q , ≤-trans m≤p p≤q , b , υ

runBindT : (A B : CC.ob) {n : ℕ} →
  ((T ⟅ A ⟆) ⟅ n ⟆) .fst →
  ((A ⇒PshLarge (T ⟅ B ⟆)) ⟅ n ⟆) .fst →
  ((T ⟅ B ⟆) ⟅ n ⟆) .fst
runBindT A B {n} t k m n≤m σ with t m n≤m σ
... | p , m≤p , a , τ =
  extendResult B m≤p
    (k .N-ob p (≤-trans n≤m m≤p , a) p ≤-refl τ)

ignoreUnit : (A : CC.ob) → T ⟅ A ⟆ ⊢ (UnitVal CC.⇒ T ⟅ A ⟆)
ignoreUnit A = CC.lda CC.π₁

------------------------------------------------------------------------
-- Store equations
------------------------------------------------------------------------

lookup-update-same : ∀ {n} (i : Fin n) (b : V .fst) (σ : Fin n → V .fst) →
  lookupStore {n = n} i (updateStore {n = n} i b σ) ≡ b
lookup-update-same {n} i b σ =
  helper (discreteFin {n = n} i i)
  where
  helper : (d : Dec (i ≡ i)) →
    decRec (λ _ → b) (λ _ → σ i) d ≡ b
  helper (yes _) = refl
  helper (no i≢i) = ⊥.rec (i≢i refl)

lookup-update-diff : ∀ {n} (i j : Fin n) →
  (i ≡ j → ⊥.⊥) → ∀ b σ →
  lookupStore {n = n} j (updateStore {n = n} i b σ) ≡
  lookupStore {n = n} j σ
lookup-update-diff {n} i j i≢j b σ =
  helper (discreteFin {n = n} i j)
  where
  helper : (d : Dec (i ≡ j)) →
    decRec (λ _ → b) (λ _ → σ j) d ≡ σ j
  helper (yes i≡j) = ⊥.rec (i≢j i≡j)
  helper (no _) = refl

update-current : ∀ {n} (i : Fin n) (σ : Fin n → V .fst) →
  updateStore {n = n} i (lookupStore {n = n} i σ) σ ≡ σ
update-current {n} i σ = funExt helper
  where
  helper-dec : (j : Fin n) (d : Dec (i ≡ j)) →
    decRec (λ _ → σ i) (λ _ → σ j) d ≡ σ j
  helper-dec j (yes i≡j) = cong σ i≡j
  helper-dec j (no _) = refl

  helper : (j : Fin n) → updateStore {n} i (σ i) σ j ≡ σ j
  helper j = helper-dec j (discreteFin {n = n} i j)

opaque
  get-set-current-store : ∀ {Γ n m}
    (i : Γ ⊢ Ref) (γ : (Γ ⟅ n ⟆) .fst)
    (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    updateStore {n = m}
      (weakenRef {n = m} {m = m} ≤-refl
        (i .N-ob m (Γ .F-hom n≤m γ)))
      (lookupStore {n = m}
        (weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)) σ)
      σ
    ≡ σ
  get-set-current-store {Γ = Γ} {n = n} {m = m} i γ n≤m σ =
    let
      r : Fin m
      r = weakenRef {n = n} {m = m} n≤m (i .N-ob n γ)
      same-reference =
        funExt⁻ (Ref .F-id {x = m})
          (i .N-ob m (Γ .F-hom n≤m γ))
        ∙ funExt⁻ (i .N-hom n≤m) γ
    in
    cong (λ r′ → updateStore {n = m} r′
      (lookupStore {n = m} r σ) σ)
      same-reference
    ∙ update-current {n = m} r σ

update-overwrite : ∀ {n} (i : Fin n) (b c : V .fst)
  (σ : Fin n → V .fst) →
  updateStore {n = n} i c (updateStore {n = n} i b σ) ≡
  updateStore {n = n} i c σ
update-overwrite {n} i b c σ = funExt helper
  where
  helper-dec : (j : Fin n) (d : Dec (i ≡ j)) →
    decRec (λ _ → c)
      (λ _ → decRec (λ _ → b) (λ _ → σ j) d) d ≡
    decRec (λ _ → c) (λ _ → σ j) d
  helper-dec j (yes _) = refl
  helper-dec j (no _) = refl

  helper : (j : Fin n) →
    updateStore {n} i c (updateStore {n} i b σ) j ≡
    updateStore {n} i c σ j
  helper j = helper-dec j (discreteFin {n = n} i j)

update-commute : ∀ {n} (i j : Fin n) →
  (i ≡ j → ⊥.⊥) → ∀ b c (σ : Fin n → V .fst) →
  updateStore {n = n} j c (updateStore {n = n} i b σ) ≡
  updateStore {n = n} i b (updateStore {n = n} j c σ)
update-commute {n} i j i≢j b c σ = funExt helper
  where
  Goal : Fin n → Type
  Goal k =
    updateStore {n} j c (updateStore {n} i b σ) k ≡
    updateStore {n} i b (updateStore {n} j c σ) k

  helper : (k : Fin n) → Goal k
  helper k = decRec case-i case-not-i (discreteFin {n = n} i k)
    where
    case-i : i ≡ k → Goal k
    case-i i≡k = decRec
      (λ j≡k → ⊥.rec (i≢j (i≡k ∙ sym j≡k)))
      (λ j≢k →
        lookup-update-diff {n} j k j≢k c (updateStore {n} i b σ) ∙
        sym (cong (updateStore {n} i b σ) i≡k) ∙
        lookup-update-same {n} i b σ ∙
        sym (lookup-update-same {n} i b (updateStore {n} j c σ)) ∙
        cong (updateStore {n} i b (updateStore {n} j c σ)) i≡k)
      (discreteFin {n = n} j k)

    case-not-i : (i ≡ k → ⊥.⊥) → Goal k
    case-not-i i≢k = decRec
      (λ j≡k →
        sym (cong (updateStore {n} j c (updateStore {n} i b σ)) j≡k) ∙
        lookup-update-same {n} j c (updateStore {n} i b σ) ∙
        sym (lookup-update-same {n} j c σ) ∙
        cong (updateStore {n} j c σ) j≡k ∙
        sym (lookup-update-diff {n} i k i≢k b
          (updateStore {n} j c σ)))
      (λ j≢k →
        lookup-update-diff {n} j k j≢k c (updateStore {n} i b σ) ∙
        lookup-update-diff {n} i k i≢k b σ ∙
        sym (lookup-update-diff {n} j k j≢k c σ) ∙
        sym (lookup-update-diff {n} i k i≢k b
          (updateStore {n} j c σ)))
      (discreteFin {n = n} j k)

extendStore-fresh : ∀ {n} b (σ : Fin n → V .fst) →
  lookupStore {n = suc n} (flast {k = n}) (extendStore {n = n} b σ) ≡ b
extendStore-fresh {n} b σ = elimFinβ {m = n} b σ .fst

extendStore-old : ∀ {n} b (σ : Fin n → V .fst) (i : Fin n) →
  lookupStore {n = suc n} (injectSuc i) (extendStore {n = n} b σ) ≡
  lookupStore {n = n} i σ
extendStore-old {n} b σ i = elimFinβ {m = n} b σ .snd i

update-fresh : ∀ {n} b c (σ : Fin n → V .fst) →
  updateStore {n = suc n} (flast {k = n}) c (extendStore {n = n} b σ) ≡
  extendStore {n = n} c σ
update-fresh {n} b c σ = funExt (elimFin {m = n} fresh old)
  where
  fresh =
    lookup-update-same {suc n} (flast {k = n}) c (extendStore {n} b σ)
    ∙ sym (extendStore-fresh {n} c σ)

  old : (i : Fin n) →
    updateStore {suc n} flast c (extendStore {n} b σ) (injectSuc i) ≡
    extendStore {n = n} c σ (injectSuc i)
  old i =
    lookup-update-diff {suc n} (flast {k = n}) (injectSuc i)
      (λ e → inject<-ne i (sym e)) c (extendStore {n} b σ)
    ∙ extendStore-old {n} b σ i
    ∙ sym (extendStore-old {n} c σ i)

extendStore-update : ∀ {n} (i : Fin n) b c (σ : Fin n → V .fst) →
  updateStore {n = suc n} (injectSuc i) c (extendStore {n = n} b σ) ≡
  extendStore {n = n} b (updateStore {n = n} i c σ)
extendStore-update {n} i b c σ = funExt (elimFin {m = n} fresh old)
  where
  fresh =
    lookup-update-diff {suc n} (injectSuc i) (flast {k = n})
      (inject<-ne i) c (extendStore {n} b σ)
    ∙ extendStore-fresh {n} b σ
    ∙ sym (extendStore-fresh {n} b (updateStore {n} i c σ))

  old : (j : Fin n) →
    updateStore {suc n} (injectSuc i) c (extendStore {n = n} b σ) (injectSuc j) ≡
    extendStore {n = n} b (updateStore {n = n} i c σ) (injectSuc j)
  old j = decRec yes-case no-case (discreteFin {n = n} i j)
    where
    yes-case = λ i≡j →
      sym (cong (updateStore {suc n} (injectSuc i) c (extendStore {n} b σ))
        (cong injectSuc i≡j))
      ∙ lookup-update-same {suc n} (injectSuc i) c (extendStore {n} b σ)
      ∙ sym (lookup-update-same {n} i c σ)
      ∙ cong (updateStore {n} i c σ) i≡j
      ∙ sym (extendStore-old {n} b (updateStore {n} i c σ) j)

    no-case = λ i≢j →
      lookup-update-diff {suc n} (injectSuc i) (injectSuc j)
        (λ e → i≢j (Σ≡Prop
          (λ a → isProp<ᵗ {n = a} {m = n}) (cong fst e))) c
        (extendStore {n} b σ)
      ∙ extendStore-old {n} b σ j
      ∙ sym (lookup-update-diff {n} i j i≢j c σ)
      ∙ sym (extendStore-old {n} b (updateStore {n} i c σ) j)

weakenRef-suc : ∀ {n} (i : Fin n) →
  weakenRef ≤-sucℕ i ≡ injectSuc i
weakenRef-suc {n} i =
  Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = suc n}) refl

-- Allocation commutes with updating an existing cell.
update-extendStore-old : ∀ {n} (i : Fin n) b c
  (σ : Fin n → V .fst) →
  updateStore {n = suc n} (weakenRef ≤-sucℕ i) c
    (extendStore {n = n} b σ) ≡
  extendStore {n = n} b (updateStore {n = n} i c σ)
update-extendStore-old {n} i b c σ =
  cong (λ j → updateStore {suc n} j c (extendStore {n} b σ))
    (weakenRef-suc {n} i)
  ∙ extendStore-update {n} i b c σ

-- Allocation commutes with reading an existing cell.
lookup-extendStore-old : ∀ {n} (i : Fin n) b
  (σ : Fin n → V .fst) →
  lookupStore {n = suc n} (weakenRef ≤-sucℕ i)
    (extendStore {n = n} b σ) ≡
  lookupStore {n = n} i σ
lookup-extendStore-old {n} i b σ =
  cong (λ j → lookupStore {n = suc n} j (extendStore {n} b σ))
    (weakenRef-suc {n} i)
  ∙ extendStore-old {n} b σ i

weakenRef-distinct : ∀ {n m} (f : n ≤ m) (i j : Fin n) →
  (i ≡ j → ⊥.⊥) → weakenRef f i ≡ weakenRef f j → ⊥.⊥
weakenRef-distinct {n} {m} f i j i≢j wi≡wj =
  i≢j (Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = n}) (cong fst wi≡wj))

------------------------------------------------------------------------
-- Computation rules
------------------------------------------------------------------------

extendResult-refl : (B : CC.ob) {m : ℕ}
  (r : ((F ⟅ B ⟆) ⟅ m ⟆) .fst) → extendResult B ≤-refl r ≡ r
extendResult-refl B (q , m≤q , b , υ) =
  ΣPathP (refl , ΣPathP (isProp≤ _ _ , ΣPathP (refl , refl)))

bindT-β : ∀ (A B : CC.ob) {n : ℕ}
  (t : ((T ⟅ A ⟆) ⟅ n ⟆) .fst)
  (k : ((A ⇒PshLarge (T ⟅ B ⟆)) ⟅ n ⟆) .fst)
  (m : ℕ) (n≤m : n ≤ m) (σ : Fin m → V .fst) →
  bindT .N-ob n (t , k) m n≤m σ ≡ runBindT A B t k m n≤m σ
bindT-β A B {n} t k m n≤m σ with t m n≤m σ
... | p , m≤p , a , τ =
  cong (extendResult B m≤p)
    (cong (λ h → k .N-ob p (h , a) p ≤-refl τ) (isProp≤ _ _))

opaque
  unfolding getᵗ setᵗ allocᵗ

  getᵗ-β : ∀ {Γ A}
    (i : Γ ⊢ Ref) (k : Γ CC.× VVal ⊢ T ⟅ A ⟆)
    n (γ : (Γ ⟅ n ⟆) .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    getᵗ i k .N-ob n γ m n≤m σ ≡
    k .N-ob m
      (Γ .F-hom n≤m γ ,
       lookupStore {n = m} (weakenRef n≤m (i .N-ob n γ)) σ)
      m ≤-refl σ
  getᵗ-β {Γ = Γ} {A = A} i k n γ m n≤m σ =
    let
      iₙ = i .N-ob n γ
      kₙ = CC.lda k .N-ob n γ
    in
    bindT-β VVal A (getM .N-ob n iₙ) kₙ m n≤m σ
    ∙ cong (extendResult A ≤-refl)
        (cong
          (λ h → kₙ .N-ob m
            (h , lookupStore {n = m} (weakenRef n≤m iₙ) σ)
            m ≤-refl σ)
          (isProp≤ _ _))
    ∙ extendResult-refl A
        (kₙ .N-ob m
          (n≤m , lookupStore {n = m} (weakenRef n≤m iₙ) σ)
          m ≤-refl σ)
    ∙ cong
        (λ q → k .N-ob m
          (Γ .F-hom q γ ,
           lookupStore {n = m} (weakenRef n≤m (i .N-ob n γ)) σ)
          m ≤-refl σ)
        (isProp≤ _ _)

  setᵗ-β : ∀ {Γ A}
    (i : Γ ⊢ Ref) (b : Γ ⊢ VVal) (t : Γ ⊢ T ⟅ A ⟆)
    n (γ : (Γ ⟅ n ⟆) .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    setᵗ i b t .N-ob n γ m n≤m σ ≡
    t .N-ob n γ m n≤m
      (updateStore {n = m} (weakenRef n≤m (i .N-ob n γ))
        (b .N-ob n γ) σ)
  setᵗ-β {A = A} i b t n γ m n≤m σ =
    let
      iₙ = i .N-ob n γ
      bₙ = b .N-ob n γ
      tₙ = t .N-ob n γ
    in
    bindT-β UnitVal A
      (setM .N-ob n (iₙ , bₙ)) (ignoreUnit A .N-ob n tₙ)
      m n≤m σ
    ∙ cong (extendResult A ≤-refl)
        (cong
          (λ h → tₙ m h
            (updateStore {n = m} (weakenRef n≤m iₙ) bₙ σ))
          (isProp≤ _ _))
    ∙ extendResult-refl A
        (tₙ m n≤m
          (updateStore {n = m} (weakenRef n≤m iₙ) bₙ σ))

  allocᵗ-β : ∀ {Γ A}
    (b : Γ ⊢ VVal) (k : Γ CC.× Ref ⊢ T ⟅ A ⟆)
    n (γ : (Γ ⟅ n ⟆) .fst) m (n≤m : n ≤ m) (σ : Fin m → V .fst) →
    allocᵗ b k .N-ob n γ m n≤m σ ≡
    extendResult A ≤-sucℕ
      (k .N-ob (suc m)
        (Γ .F-hom (≤-trans n≤m ≤-sucℕ) γ , flast {k = m})
        (suc m) ≤-refl (extendStore {n = m} (b .N-ob n γ) σ))
  allocᵗ-β {Γ = Γ} {A = A} b k n γ m n≤m σ =
    bindT-β Ref A
      (allocM .N-ob n (b .N-ob n γ))
      (CC.lda k .N-ob n γ) m n≤m σ
    ∙ cong (extendResult A ≤-sucℕ)
        (cong
          (λ q → k .N-ob (suc m)
            (Γ .F-hom q γ , flast {k = m})
            (suc m) ≤-refl (extendStore {n = m} (b .N-ob n γ) σ))
          (isProp≤ _ _))
