open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet ; isSet→)

import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Properties using (elimFinβ ; inject<-ne)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive using (<→<ᵗ ; <ᵗ→< ; isProp<ᵗ)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant using (Constant)
open import Cubical.Categories.Instances.Discrete.More
  using (EqDiscreteCategory ; EqDiscFunc)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Instances.Thin using (ThinCategory)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
  using (-×Psh_)
open import Cubical.Categories.Presheaf.Constructions.Reindex using (reindPshF)

module Cubical.Categories.Monad.Instances.LocalState.Levy.Base
  (V : hSet ℓ-zero) where

open Category
open Functor
open NatTrans
open UnitCounit

------------------------------------------------------------------------
-- Worlds and presheaf categories
------------------------------------------------------------------------

World : Category ℓ-zero ℓ-zero
World = ThinCategory ℕ _≤_ ≤-refl ≤-trans isProp≤

|World| : Category ℓ-zero ℓ-zero
|World| = EqDiscreteCategory ℕ isSetℕ

include : Functor |World| World
include = EqDiscFunc (λ n → n)

includeOp : Functor |World| (World ^op)
includeOp = EqDiscFunc (λ n → n)

-- Values vary covariantly with world extension, computations contravariantly.
-- Writing both as presheaf categories makes the Kan-extension interface apply
-- directly.
Val : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Val ℓ = PresheafCategory (World ^op) ℓ

Comp : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Comp ℓ = PresheafCategory World ℓ

WorldFam : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
WorldFam ℓ = PresheafCategory |World| ℓ

includeOp* : (ℓ : Level) → Functor (Val ℓ) (WorldFam ℓ)
includeOp* ℓ = reindPshF includeOp

include* : (ℓ : Level) → Functor (Comp ℓ) (WorldFam ℓ)
include* ℓ = reindPshF include

S : WorldFam ℓ-zero .ob
S .F-ob n .fst = Fin n → V .fst
S .F-ob n .snd = isSet→ (V .snd)
S .F-hom Eq.refl = λ σ → σ
S .F-id = refl
S .F-seq Eq.refl Eq.refl = refl

VVal : Val ℓ-zero .ob
VVal = Constant ((World ^op) ^op) (SET ℓ-zero) V

UnitVal : Val ℓ-zero .ob
UnitVal = Constant ((World ^op) ^op) (SET ℓ-zero) (Unit , isSetUnit)

weakenRef : ∀ {n m} → n ≤ m → Fin n → Fin m
weakenRef {n} {m} n≤m (i , i<n) =
  i , <→<ᵗ (<≤-trans (<ᵗ→< i<n) n≤m)

Ref : Val ℓ-zero .ob
Ref .F-ob n = Fin n , isSetFin {k = n}
Ref .F-hom {x = n} {y = m} f = weakenRef {n = n} {m = m} f
Ref .F-id {x = n} =
  funExt λ (_ : Fin n) →
    Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = n}) refl
Ref .F-seq {x = n} {y = m} {z = p} f g =
  funExt λ (_ : Fin n) →
    Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = p}) refl

-×S : Functor (WorldFam ℓ-zero) (WorldFam ℓ-zero)
-×S = -×Psh S

S⇒- : Functor (WorldFam ℓ-zero) (WorldFam ℓ-zero)
S⇒- .F-ob A .F-ob n .fst = S .F-ob n .fst → A .F-ob n .fst
S⇒- .F-ob A .F-ob n .snd = isSet→ (A .F-ob n .snd)
S⇒- .F-ob A .F-hom Eq.refl = λ k → k
S⇒- .F-ob A .F-id = refl
S⇒- .F-ob A .F-seq Eq.refl Eq.refl = refl
S⇒- .F-hom α .N-ob n k = λ s → α .N-ob n (k s)
S⇒- .F-hom α .N-hom Eq.refl = refl
S⇒- .F-id = makeNatTransPath refl
S⇒- .F-seq α β = makeNatTransPath refl

-×S⊣S⇒- : -×S ⊣ S⇒-
-×S⊣S⇒- ._⊣_.η .N-ob A .N-ob n a s = a , s
-×S⊣S⇒- ._⊣_.η .N-ob A .N-hom Eq.refl =
  funExt λ a → funExt λ s → ΣPathP (funExt⁻ (A .F-id) a , refl)
-×S⊣S⇒- ._⊣_.η .N-hom α = makeNatTransPath refl
-×S⊣S⇒- ._⊣_.ε .N-ob A .N-ob n (k , s) = k s
-×S⊣S⇒- ._⊣_.ε .N-ob A .N-hom Eq.refl =
  funExt λ (k , s) → sym (funExt⁻ (A .F-id) (k s))
-×S⊣S⇒- ._⊣_.ε .N-hom α = makeNatTransPath refl
-×S⊣S⇒- ._⊣_.triangleIdentities .TriangleIdentities.Δ₁ A =
  makeNatTransPath refl
-×S⊣S⇒- ._⊣_.triangleIdentities .TriangleIdentities.Δ₂ A =
  makeNatTransPath refl

------------------------------------------------------------------------
-- Store operations and laws
------------------------------------------------------------------------

lookupStore : ∀ {n} → Fin n → (Fin n → V .fst) → V .fst
lookupStore i σ = σ i

updateStore : ∀ {n} → Fin n → V .fst → (Fin n → V .fst) → Fin n → V .fst
updateStore {n} i b σ j =
  decRec (λ _ → b) (λ _ → σ j) (discreteFin {n = n} i j)

lookup-update-same : ∀ {n} (i : Fin n) (b : V .fst) (σ : Fin n → V .fst) →
  lookupStore {n = n} i (updateStore {n = n} i b σ) ≡ b
lookup-update-same {n} i b σ =
  helper (discreteFin {n = n} i i)
  where
  helper : (d : Dec (i ≡ i)) →
    decRec (λ _ → b) (λ _ → σ i) d ≡ b
  helper (yes _) = refl
  helper (no i≢i) = ⊥.rec (i≢i refl)

lookup-update-diff : ∀ {n} (i j : Fin n) → ((i ≡ j) → ⊥.⊥) → ∀ b σ →
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

update-overwrite : ∀ {n} (i : Fin n) (b c : V .fst) (σ : Fin n → V .fst) →
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

update-commute : ∀ {n} (i j : Fin n) → ((i ≡ j) → ⊥.⊥) → ∀ b c (σ : Fin n → V .fst) →
  updateStore {n = n} j c (updateStore {n = n} i b σ) ≡
  updateStore {n = n} i b (updateStore {n = n} j c σ)
update-commute {n} i j i≢j b c σ = funExt helper
  where
  Goal : Fin n → Type
  Goal k =
    updateStore {n} j c (updateStore {n} i b σ) k ≡
    updateStore {n} i b (updateStore {n} j c σ) k

  helper : (k : Fin n) →
    updateStore {n} j c (updateStore {n} i b σ) k ≡
    updateStore {n} i b (updateStore {n} j c σ) k
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

    case-not-i : ((i ≡ k) → ⊥.⊥) → Goal k
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

-- Extend a store by appending a new cell.  The fresh location is `flast`.
extendStore : ∀ {n} → V .fst → (Fin n → V .fst) → Fin (suc n) → V .fst
extendStore {n} b σ = elimFin {m = n} b σ

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
  fresh = lookup-update-same {suc n} (flast {k = n}) c (extendStore {n} b σ)
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

------------------------------------------------------------------------
-- Reference weakening
------------------------------------------------------------------------

weakenRef-comp :
  ∀ {n m p} (f : n ≤ m) (g : m ≤ p) (i : Fin n) →
  weakenRef {n = m} {m = p} g (weakenRef {n = n} {m = m} f i) ≡
  weakenRef {n = n} {m = p} (≤-trans f g) i
weakenRef-comp {n} {m} {p} f g i =
  Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = p}) refl

weakenRef-distinct : ∀ {n m} (f : n ≤ m) (i j : Fin n) →
  ((i ≡ j) → ⊥.⊥) → (weakenRef f i ≡ weakenRef f j) → ⊥.⊥
weakenRef-distinct {n} {m} f i j i≠j wi≡wj =
  i≠j (Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = n}) (cong fst wi≡wj))

weakenRef-suc : ∀ {n} (i : Fin n) →
  weakenRef ≤-sucℕ i ≡ injectSuc i
weakenRef-suc {n} i =
  Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = suc n}) refl

------------------------------------------------------------------------
-- Allocation and existing cells
------------------------------------------------------------------------

-- Allocation commutes with updating an existing cell.
update-extendStore-old : ∀ {n} (i : Fin n) b c (σ : Fin n → V .fst) →
  updateStore {n = suc n} (weakenRef ≤-sucℕ i) c
    (extendStore {n = n} b σ) ≡
  extendStore {n = n} b (updateStore {n = n} i c σ)
update-extendStore-old {n} i b c σ =
  cong (λ j → updateStore {suc n} j c (extendStore {n} b σ))
    (weakenRef-suc {n} i)
  ∙ extendStore-update {n} i b c σ

-- Allocation commutes with reading an existing cell.
lookup-extendStore-old : ∀ {n} (i : Fin n) b (σ : Fin n → V .fst) →
  lookupStore {n = suc n} (weakenRef ≤-sucℕ i)
    (extendStore {n = n} b σ) ≡
  lookupStore {n = n} i σ
lookup-extendStore-old {n} i b σ =
  cong (λ j → lookupStore {n = suc n} j (extendStore {n} b σ))
    (weakenRef-suc {n} i)
  ∙ extendStore-old {n} b σ i

------------------------------------------------------------------------
-- Limitation of the single-cell interface
------------------------------------------------------------------------

{- The indexed block law B3ₙ compares allocation of an n-cell block with n
   iterated single-cell allocations, modulo a permutation/renaming of the
   fresh references.  The current signature only supplies

     alloc : V .fst × (Ref ⇒ T A) ⇒ T A,

   and has neither an n-ary reference object nor an explicit renaming action.
   Thus B3ₙ is not merely unproved: it cannot be stated faithfully using this
   single-cell operation and this permutation-free world category.
-}
