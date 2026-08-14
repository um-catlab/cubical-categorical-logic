{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Monad.Instances.LocalState.Levy.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
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

open Category
open Functor
open NatTrans
open UnitCounit

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
Values : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Values ℓ = PresheafCategory (World ^op) ℓ

Computations : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Computations ℓ = PresheafCategory World ℓ

WorldFam : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
WorldFam ℓ = PresheafCategory |World| ℓ

includeOp* : (ℓ : Level) → Functor (Values ℓ) (WorldFam ℓ)
includeOp* ℓ = reindPshF includeOp

include* : (ℓ : Level) → Functor (Computations ℓ) (WorldFam ℓ)
include* ℓ = reindPshF include

S : WorldFam ℓ-zero .ob
S .F-ob n .fst = Fin n → Bool
S .F-ob n .snd = isSet→ isSetBool
S .F-hom Eq.refl = λ σ → σ
S .F-id = refl
S .F-seq Eq.refl Eq.refl = refl

lookupStore : ∀ {n} → Fin n → (Fin n → Bool) → Bool
lookupStore i σ = σ i

updateStore : ∀ {n} → Fin n → Bool → (Fin n → Bool) → Fin n → Bool
updateStore i b σ j with discreteFin i j
... | yes _ = b
... | no  _ = σ j

lookup-update-same : ∀ {n} (i : Fin n) b σ →
  lookupStore i (updateStore i b σ) ≡ b
lookup-update-same i b σ with discreteFin i i
... | yes _ = refl
... | no i≢i = ⊥.rec (i≢i refl)

lookup-update-diff : ∀ {n} (i j : Fin n) → ((i ≡ j) → ⊥.⊥) → ∀ b σ →
  lookupStore j (updateStore i b σ) ≡ lookupStore j σ
lookup-update-diff i j i≢j b σ with discreteFin i j
... | yes i≡j = ⊥.rec (i≢j i≡j)
... | no _ = refl

update-current : ∀ {n} (i : Fin n) (σ : Fin n → Bool) →
  updateStore i (lookupStore i σ) σ ≡ σ
update-current i σ = funExt helper
  where
  helper : (j : _) → updateStore i (σ i) σ j ≡ σ j
  helper j with discreteFin i j
  ... | yes i≡j = cong σ i≡j
  ... | no _ = refl

update-overwrite : ∀ {n} (i : Fin n) b c (σ : Fin n → Bool) →
  updateStore i c (updateStore i b σ) ≡ updateStore i c σ
update-overwrite i b c σ = funExt helper
  where
  helper : (j : _) →
    updateStore i c (updateStore i b σ) j ≡ updateStore i c σ j
  helper j with discreteFin i j
  ... | yes _ = refl
  ... | no i≢j = lookup-update-diff i j i≢j b σ

update-commute : ∀ {n} (i j : Fin n) → ((i ≡ j) → ⊥.⊥) → ∀ b c (σ : Fin n → Bool) →
  updateStore j c (updateStore i b σ) ≡
  updateStore i b (updateStore j c σ)
update-commute i j i≢j b c σ = funExt helper
  where
  helper : (k : _) →
    updateStore j c (updateStore i b σ) k ≡
    updateStore i b (updateStore j c σ) k
  helper k with discreteFin i k | discreteFin j k
  ... | yes i≡k | yes j≡k = ⊥.rec (i≢j (i≡k ∙ sym j≡k))
  ... | yes i≡k | no _ =
    sym (cong (updateStore i b σ) i≡k) ∙ lookup-update-same i b σ
  ... | no _ | yes j≡k =
    sym (lookup-update-same j c σ) ∙ cong (updateStore j c σ) j≡k
  ... | no i≢k | no j≢k =
    lookup-update-diff i k i≢k b σ
    ∙ sym (lookup-update-diff j k j≢k c σ)

-- Extend a store by appending a new cell.  The fresh location is `flast`.
extendStore : ∀ {n} → Bool → (Fin n → Bool) → Fin (suc n) → Bool
extendStore b σ = elimFin b σ

extendStore-fresh : ∀ {n} b (σ : Fin n → Bool) →
  lookupStore flast (extendStore b σ) ≡ b
extendStore-fresh b σ = elimFinβ b σ .fst

extendStore-old : ∀ {n} b (σ : Fin n → Bool) (i : Fin n) →
  lookupStore (injectSuc i) (extendStore b σ) ≡ lookupStore i σ
extendStore-old b σ i = elimFinβ b σ .snd i

update-fresh : ∀ {n} b c (σ : Fin n → Bool) →
  updateStore flast c (extendStore b σ) ≡ extendStore c σ
update-fresh b c σ = funExt (elimFin fresh old)
  where
  fresh = lookup-update-same flast c (extendStore b σ)
    ∙ sym (extendStore-fresh c σ)
  old : (i : _) →
    updateStore flast c (extendStore b σ) (injectSuc i) ≡
    extendStore c σ (injectSuc i)
  old i =
    lookup-update-diff flast (injectSuc i) (λ e → inject<-ne i (sym e)) c (extendStore b σ)
    ∙ extendStore-old b σ i
    ∙ sym (extendStore-old c σ i)

extendStore-update : ∀ {n} (i : Fin n) b c (σ : Fin n → Bool) →
  updateStore (injectSuc i) c (extendStore b σ) ≡
  extendStore b (updateStore i c σ)
extendStore-update i b c σ = funExt (elimFin fresh old)
  where
  fresh =
    lookup-update-diff (injectSuc i) flast (inject<-ne i) c (extendStore b σ)
    ∙ extendStore-fresh b σ
    ∙ sym (extendStore-fresh b (updateStore i c σ))
  old : (j : _) →
    updateStore (injectSuc i) c (extendStore b σ) (injectSuc j) ≡
    extendStore b (updateStore i c σ) (injectSuc j)
  old j with discreteFin i j
  ... | yes i≡j =
    sym (cong (updateStore (injectSuc i) c (extendStore b σ)) (cong injectSuc i≡j))
    ∙ lookup-update-same (injectSuc i) c (extendStore b σ)
    ∙ sym (lookup-update-same i c σ)
    ∙ cong (updateStore i c σ) i≡j
    ∙ sym (extendStore-old b (updateStore i c σ) j)
  ... | no i≢j =
    lookup-update-diff (injectSuc i) (injectSuc j)
      (λ e → i≢j (Σ≡Prop (λ _ → isProp<ᵗ) (cong fst e))) c (extendStore b σ)
    ∙ extendStore-old b σ j
    ∙ sym (lookup-update-diff i j i≢j c σ)
    ∙ sym (extendStore-old b (updateStore i c σ) j)

weakenRef : ∀ {n m} → n ≤ m → Fin n → Fin m
weakenRef n≤m (i , i<n) =
  i , <→<ᵗ (<≤-trans (<ᵗ→< i<n) n≤m)

weakenRef-comp :
  ∀ {n m p} (f : n ≤ m) (g : m ≤ p) (i : Fin n) →
  weakenRef g (weakenRef f i) ≡ weakenRef (≤-trans f g) i
weakenRef-comp f g i = Σ≡Prop (λ _ → isProp<ᵗ) refl

BoolVal : Values ℓ-zero .ob
BoolVal = Constant ((World ^op) ^op) (SET ℓ-zero) (Bool , isSetBool)

UnitVal : Values ℓ-zero .ob
UnitVal = Constant ((World ^op) ^op) (SET ℓ-zero) (Unit , isSetUnit)

Ref : Values ℓ-zero .ob
Ref .F-ob n = Fin n , isSetFin
Ref .F-hom f = weakenRef f
Ref .F-id = funExt λ i → Σ≡Prop (λ _ → isProp<ᵗ) refl
Ref .F-seq f g = funExt λ i → Σ≡Prop (λ _ → isProp<ᵗ) refl

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
