{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Monad.Instances.LocalState.Levy.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv using (funExt₃)

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
open import Cubical.HITs.SetQuotients

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Monad
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Instances.Discrete.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Thin
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.KanExtension
import Cubical.Categories.Presheaf.KanExtension.Discrete as DiscreteKan
open import Cubical.Categories.Presheaf.Morphism.Alt

open Category
open Functor
open NatTrans
open UnitCounit

World : Category ℓ-zero ℓ-zero
World = ThinCategory ℕ _≤_ ≤-refl ≤-trans isProp≤

|World| : Category ℓ-zero ℓ-zero
|World| = EqDiscreteCategory ℕ isSetℕ

-- The identity-on-objects inclusions into future- and past-directed worlds.
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

-- Forget the action of a value or computation on genuine world extensions.
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
freshStore : ∀ {n} → Bool → (Fin n → Bool) → Fin (suc n) → Bool
freshStore b σ = elimFin b σ

freshStore-fresh : ∀ {n} b (σ : Fin n → Bool) →
  lookupStore flast (freshStore b σ) ≡ b
freshStore-fresh b σ = elimFinβ b σ .fst

freshStore-old : ∀ {n} b (σ : Fin n → Bool) (i : Fin n) →
  lookupStore (injectSuc i) (freshStore b σ) ≡ lookupStore i σ
freshStore-old b σ i = elimFinβ b σ .snd i

update-fresh : ∀ {n} b c (σ : Fin n → Bool) →
  updateStore flast c (freshStore b σ) ≡ freshStore c σ
update-fresh b c σ = funExt (elimFin fresh old)
  where
  fresh = lookup-update-same flast c (freshStore b σ)
    ∙ sym (freshStore-fresh c σ)
  old : (i : _) →
    updateStore flast c (freshStore b σ) (injectSuc i) ≡
    freshStore c σ (injectSuc i)
  old i =
    lookup-update-diff flast (injectSuc i) (λ e → inject<-ne i (sym e)) c (freshStore b σ)
    ∙ freshStore-old b σ i
    ∙ sym (freshStore-old c σ i)

freshStore-update : ∀ {n} (i : Fin n) b c (σ : Fin n → Bool) →
  updateStore (injectSuc i) c (freshStore b σ) ≡
  freshStore b (updateStore i c σ)
freshStore-update i b c σ = funExt (elimFin fresh old)
  where
  fresh =
    lookup-update-diff (injectSuc i) flast (inject<-ne i) c (freshStore b σ)
    ∙ freshStore-fresh b σ
    ∙ sym (freshStore-fresh b (updateStore i c σ))
  old : (j : _) →
    updateStore (injectSuc i) c (freshStore b σ) (injectSuc j) ≡
    freshStore b (updateStore i c σ) (injectSuc j)
  old j with discreteFin i j
  ... | yes i≡j =
    sym (cong (updateStore (injectSuc i) c (freshStore b σ)) (cong injectSuc i≡j))
    ∙ lookup-update-same (injectSuc i) c (freshStore b σ)
    ∙ sym (lookup-update-same i c σ)
    ∙ cong (updateStore i c σ) i≡j
    ∙ sym (freshStore-old b (updateStore i c σ) j)
  ... | no i≢j =
    lookup-update-diff (injectSuc i) (injectSuc j)
      (λ e → i≢j (Σ≡Prop (λ _ → isProp<ᵗ) (cong fst e))) c (freshStore b σ)
    ∙ freshStore-old b σ j
    ∙ sym (lookup-update-diff i j i≢j c σ)
    ∙ sym (freshStore-old b (updateStore i c σ) j)

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

-- This is the computational presentation: the discrete Kan extensions are
-- literally a dependent sum and dependent product.
module Discrete where
  LanΣ : Functor (WorldFam ℓ-zero) (Computations ℓ-zero)
  LanΣ = DiscreteKan.Lan ℓ-zero isSetℕ include

  RanΠ : Functor (WorldFam ℓ-zero) (Values ℓ-zero)
  RanΠ = DiscreteKan.Ran ℓ-zero isSetℕ includeOp

  LanΣ⊣include* : LanΣ ⊣ include* ℓ-zero
  LanΣ⊣include* = DiscreteKan.Lan⊣J* ℓ-zero isSetℕ include

  includeOp*⊣RanΠ : includeOp* ℓ-zero ⊣ RanΠ
  includeOp*⊣RanΠ = DiscreteKan.J*⊣Ran ℓ-zero isSetℕ includeOp

  F : Functor (Values ℓ-zero) (Computations ℓ-zero)
  F = LanΣ ∘F (-×S ∘F includeOp* ℓ-zero)

  U : Functor (Computations ℓ-zero) (Values ℓ-zero)
  U = (RanΠ ∘F S⇒-) ∘F include* ℓ-zero

  F⊣U : F ⊣ U
  F⊣U = adj'→adj F U
    (Compose.LF⊣GR
      (Compose.LF⊣GR
        (adj→adj' (includeOp* ℓ-zero) RanΠ includeOp*⊣RanΠ)
        (adj→adj' -×S S⇒- -×S⊣S⇒-))
      (adj→adj' LanΣ (include* ℓ-zero) LanΣ⊣include*))

  T : Functor (Values ℓ-zero) (Values ℓ-zero)
  T = U ∘F F

  T[_] : Values ℓ-zero .ob → Type
  T[ A ] =
    (n m : ℕ) → n ≤ m → (Fin m → Bool) →
    Σ[ p ∈ ℕ ] (m ≤ p) × (A .F-ob p .fst × (Fin p → Bool))

  ComputationAt : Values ℓ-zero .ob → ℕ → Type
  ComputationAt A n =
    (m : ℕ) → n ≤ m → (Fin m → Bool) →
    Σ[ p ∈ ℕ ] (m ≤ p) × (A .F-ob p .fst × (Fin p → Bool))

  getOp : ∀ {A n} → Fin n → (Bool → ComputationAt A n) → ComputationAt A n
  getOp i k m n≤m σ = k (lookupStore (weakenRef n≤m i) σ) m n≤m σ

  setOp : ∀ {A n} → Fin n → Bool → ComputationAt A n → ComputationAt A n
  setOp i b t m n≤m σ =
    t m n≤m (updateStore (weakenRef n≤m i) b σ)

  weakenRef-distinct : ∀ {n m} (f : n ≤ m) (i j : Fin n) →
    ((i ≡ j) → ⊥.⊥) → (weakenRef f i ≡ weakenRef f j) → ⊥.⊥
  weakenRef-distinct f i j i≢j wi≡wj =
    i≢j (Σ≡Prop (λ _ → isProp<ᵗ) (cong fst wi≡wj))

  get-get-same : ∀ {A n} (i : Fin n)
    (k : Bool → Bool → ComputationAt A n) →
    getOp {A = A} i (λ b → getOp {A = A} i (λ c → k b c)) ≡
    getOp {A = A} i (λ b → k b b)
  get-get-same i k = refl

  get-set-same : ∀ {A n} (i : Fin n) (t : ComputationAt A n) →
    getOp {A = A} i (λ b → setOp {A = A} i b t) ≡ t
  get-set-same i t = funExt₃ λ m n≤m σ →
    cong (t m n≤m) (update-current (weakenRef n≤m i) σ)

  set-get-same : ∀ {A n} (i : Fin n) b
    (k : Bool → ComputationAt A n) →
    setOp {A = A} i b (getOp {A = A} i k) ≡ setOp {A = A} i b (k b)
  set-get-same i b k = funExt₃ λ m n≤m σ →
    cong
      (λ c → k c m n≤m
        (updateStore (weakenRef n≤m i) b σ))
      (lookup-update-same (weakenRef n≤m i) b σ)

  set-set-same : ∀ {A n} (i : Fin n) b c
    (t : ComputationAt A n) →
    setOp {A = A} i b (setOp {A = A} i c t) ≡ setOp {A = A} i c t
  set-set-same i b c t = funExt₃ λ m n≤m σ →
    cong (t m n≤m) (update-overwrite (weakenRef n≤m i) b c σ)

  -- missing distinct assumption?
  get-get-distinct : ∀ {A n} (i j : Fin n)
    (k : Bool → Bool → ComputationAt A n) →
    getOp {A = A} i (λ b → getOp {A = A} j (λ c → k b c)) ≡
    getOp {A = A} j (λ c → getOp {A = A} i (λ b → k b c))
  get-get-distinct i j k = refl

  set-set-distinct : ∀ {A n} (i j : Fin n) →
    ((i ≡ j) → ⊥.⊥) → ∀ b c (t : ComputationAt A n) →
    setOp {A = A} i b (setOp {A = A} j c t) ≡
    setOp {A = A} j c (setOp {A = A} i b t)
  set-set-distinct i j i≢j b c t = funExt₃ λ m n≤m σ →
    cong (t m n≤m)
      (update-commute (weakenRef n≤m i) (weakenRef n≤m j)
        (weakenRef-distinct n≤m i j i≢j) b c σ)

  set-get-distinct : ∀ {A n} (i j : Fin n) →
    ((i ≡ j) → ⊥.⊥) → ∀ b
    (k : Bool → ComputationAt A n) →
    setOp {A = A} i b (getOp {A = A} j k) ≡
    getOp {A = A} j (λ c → setOp {A = A} i b (k c))
  set-get-distinct i j i≢j b k = funExt₃ λ m n≤m σ →
    cong
      (λ c → k c m n≤m
        (updateStore (weakenRef n≤m i) b σ))
      (lookup-update-diff (weakenRef n≤m i) (weakenRef n≤m j)
        (weakenRef-distinct n≤m i j i≢j) b σ)

  weakenRef-suc : ∀ {n} (i : Fin n) →
    weakenRef ≤-sucℕ i ≡ injectSuc i
  weakenRef-suc i = Σ≡Prop (λ _ → isProp<ᵗ) refl

  -- Updating the newly allocated cell replaces its initial value.
  LS1 : ∀ {n} b c (σ : Fin n → Bool) →
    updateStore flast c (freshStore b σ) ≡ freshStore c σ
  LS1 = update-fresh

  -- Reading the newly allocated cell returns its initial value.
  LS2 : ∀ {n} b (σ : Fin n → Bool) →
    lookupStore flast (freshStore b σ) ≡ b
  LS2 = freshStore-fresh

  -- Allocation commutes with updating an existing cell.
  LS3 : ∀ {n} (i : Fin n) b c (σ : Fin n → Bool) →
    updateStore (weakenRef ≤-sucℕ i) c (freshStore b σ) ≡
    freshStore b (updateStore i c σ)
  LS3 i b c σ =
    cong (λ j → updateStore j c (freshStore b σ)) (weakenRef-suc i)
    ∙ freshStore-update i b c σ

  -- Allocation commutes with reading an existing cell.
  LS4 : ∀ {n} (i : Fin n) b (σ : Fin n → Bool) →
    lookupStore (weakenRef ≤-sucℕ i) (freshStore b σ) ≡
    lookupStore i σ
  LS4 i b σ =
    cong (λ j → lookupStore j (freshStore b σ)) (weakenRef-suc i)
    ∙ freshStore-old b σ i

  LS : Monad (Values ℓ-zero)
  LS = T , MonadFromAdjunction F U F⊣U

  get : NatTrans Ref (T .F-ob BoolVal)
  get .N-ob n i m n≤m σ =
    m , ≤-refl , lookupStore (weakenRef n≤m i) σ , σ
  get .N-hom f =
    funExt λ i → funExt λ m → funExt λ q → funExt λ σ →
      cong
        {B = λ _ →
          Σ[ p ∈ ℕ ] (m ≤ p) ×
            (BoolVal .F-ob p .fst × (Fin p → Bool))}
        (λ j → m , ≤-refl , lookupStore j σ , σ)
        (weakenRef-comp f q i)

  set : NatTrans (Ref ×Psh BoolVal) (T .F-ob UnitVal)
  set .N-ob n (i , b) m n≤m σ =
    m , ≤-refl , tt , updateStore (weakenRef n≤m i) b σ
  set .N-hom f =
    funExt λ (i , b) → funExt λ m → funExt λ q → funExt λ σ →
      cong
        {B = λ _ →
          Σ[ p ∈ ℕ ] (m ≤ p) ×
            (UnitVal .F-ob p .fst × (Fin p → Bool))}
        (λ j → m , ≤-refl , tt , updateStore j b σ)
        (weakenRef-comp f q i)

  alloc : NatTrans BoolVal (T .F-ob Ref)
  alloc .N-ob n b m n≤m σ =
    suc m , ≤-sucℕ , flast , freshStore b σ
  alloc .N-hom f =
    funExt λ b → funExt λ m → funExt λ q → funExt λ σ → refl

  getOpNT : (A : Values ℓ-zero .ob) →
    NatTrans (Ref ×Psh (BoolVal ⇒PshLarge (T .F-ob A))) (T .F-ob A)
  getOpNT A .N-ob n (i , k) m n≤m σ =
    k .PshHom.N-ob m (n≤m , lookupStore (weakenRef n≤m i) σ)
      m ≤-refl σ
  getOpNT A .N-hom f =
    funExt λ (i , k) → funExt₃ λ m q σ →
      cong
        (λ j → k .PshHom.N-ob m
          (≤-trans f q , lookupStore j σ) m ≤-refl σ)
        (weakenRef-comp f q i)

  setOpNT : (A : Values ℓ-zero .ob) →
    NatTrans ((Ref ×Psh BoolVal) ×Psh (T .F-ob A)) (T .F-ob A)
  setOpNT A .N-ob n ((i , b) , t) m n≤m σ =
    t m n≤m (updateStore (weakenRef n≤m i) b σ)
  setOpNT A .N-hom f =
    funExt λ ((i , b) , t) → funExt₃ λ m q σ →
      cong
        (t m (≤-trans f q))
        (cong (λ j → updateStore j b σ) (weakenRef-comp f q i))

  lowerAllocResult : (A : Values ℓ-zero .ob) (m : ℕ) →
    Σ[ p ∈ ℕ ] (suc m ≤ p) × (A .F-ob p .fst × (Fin p → Bool)) →
    Σ[ p ∈ ℕ ] (m ≤ p) × (A .F-ob p .fst × (Fin p → Bool))
  lowerAllocResult A m (p , sm≤p , a , τ) =
    p , ≤-trans ≤-sucℕ sm≤p , a , τ

  allocOpNT : (A : Values ℓ-zero .ob) →
    NatTrans (BoolVal ×Psh (Ref ⇒PshLarge (T .F-ob A))) (T .F-ob A)
  allocOpNT A .N-ob n (b , k) m n≤m σ = lowerAllocResult A m
    (k .PshHom.N-ob (suc m) (≤-trans n≤m ≤-sucℕ , flast)
      (suc m) ≤-refl (freshStore b σ))
  allocOpNT A .N-hom f =
    funExt λ (b , k) → funExt₃ λ m q σ →
      cong
        (λ r → lowerAllocResult A m
          (k .PshHom.N-ob (suc m) (r , flast)
            (suc m) ≤-refl (freshStore b σ)))
        (isProp≤ _ _)

-- This is the original library presentation through a coend quotient and an
-- end carrying its coherence field.
module Original where
  Lan-include⊣include* :
    Lan.Lan ℓ-zero include ⊣ include* ℓ-zero
  Lan-include⊣include* = Lan.adj ℓ-zero include

  includeOp*⊣Ran-includeOp :
    includeOp* ℓ-zero ⊣ Ran.Ran ℓ-zero includeOp
  includeOp*⊣Ran-includeOp = Ran.adj ℓ-zero includeOp

  F : Functor (Values ℓ-zero) (Computations ℓ-zero)
  F = Lan.Lan ℓ-zero include ∘F (-×S ∘F includeOp* ℓ-zero)

  U : Functor (Computations ℓ-zero) (Values ℓ-zero)
  U = (Ran.Ran ℓ-zero includeOp ∘F S⇒-) ∘F include* ℓ-zero

  F⊣U : F ⊣ U
  F⊣U = adj'→adj F U
    (Compose.LF⊣GR
      (Compose.LF⊣GR
        (adj→adj' (includeOp* ℓ-zero) (Ran.Ran ℓ-zero includeOp)
          includeOp*⊣Ran-includeOp)
        (adj→adj' -×S S⇒- -×S⊣S⇒-))
      (adj→adj' (Lan.Lan ℓ-zero include) (include* ℓ-zero)
        Lan-include⊣include*))

  T : Functor (Values ℓ-zero) (Values ℓ-zero)
  T = U ∘F F

  LS : Monad (Values ℓ-zero)
  LS = T , MonadFromAdjunction F U F⊣U

  module Outer = Ran ℓ-zero includeOp
  module Inner = Lan ℓ-zero include

  now : (A : Values ℓ-zero .ob) (n : ℕ) →
    A .F-ob n .fst → S .F-ob n .fst →
    Inner.Quo ((-×S ∘F includeOp* ℓ-zero) .F-ob A) n
  now A n a σ = [ (n , ≤-refl , (a , σ)) ]

  get : NatTrans Ref (T .F-ob BoolVal)
  get .N-ob n i .Outer.End.fun m n≤m σ =
    now BoolVal m (lookupStore (weakenRef n≤m i) σ) σ
  get .N-ob n i .Outer.End.coh Eq.refl n≤m =
    funExt λ σ →
      cong (λ j → now BoolVal _ (lookupStore j σ) σ)
        (Σ≡Prop (λ _ → isProp<ᵗ) refl)
  get .N-hom f =
    funExt λ i → Outer.end≡ _ λ m q → funExt λ σ →
      cong (λ j → now BoolVal m (lookupStore j σ) σ)
        (Σ≡Prop (λ _ → isProp<ᵗ) refl)

  set : NatTrans (Ref ×Psh BoolVal) (T .F-ob UnitVal)
  set .N-ob n (i , b) .Outer.End.fun m n≤m σ =
    now UnitVal m tt (updateStore (weakenRef n≤m i) b σ)
  set .N-ob n (i , b) .Outer.End.coh Eq.refl n≤m =
    funExt λ σ →
      cong (λ j → now UnitVal _ tt (updateStore j b σ))
        (Σ≡Prop (λ _ → isProp<ᵗ) refl)
  set .N-hom f =
    funExt λ (i , b) → Outer.end≡ _ λ m q → funExt λ σ →
      cong (λ j → now UnitVal m tt (updateStore j b σ))
        (Σ≡Prop (λ _ → isProp<ᵗ) refl)

  alloc : NatTrans BoolVal (T .F-ob Ref)
  alloc .N-ob n b .Outer.End.fun m n≤m σ =
    [ (suc m , ≤-sucℕ , (flast , freshStore b σ)) ]
  alloc .N-ob n b .Outer.End.coh Eq.refl n≤m = refl
  alloc .N-hom f =
    funExt λ b → Outer.end≡ _ λ m q → funExt λ σ → refl
