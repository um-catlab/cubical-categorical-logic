{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Monad.Instances.LocalState.Levy.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Functions.FunExtEquiv using (funExt₃)

open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive using (isProp<ᵗ)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Monad using (MonadFromAdjunction)
open import Cubical.Categories.Functor
open import Cubical.Categories.Monad.Base using (Monad)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base using (_×Psh_)
open import Cubical.Categories.Presheaf.Constructions.Exponential using (_⇒PshLarge_)
import Cubical.Categories.Presheaf.KanExtension.Discrete as DiscreteKan
open import Cubical.Categories.Presheaf.Morphism.Alt

open Category
open Functor
open NatTrans
open UnitCounit

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base

-- Computational presentation using dependent sums and products.
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

LS : Monad (Values ℓ-zero)
LS = T , MonadFromAdjunction F U F⊣U

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
alloc-set-same : ∀ {n} b c (σ : Fin n → Bool) →
  updateStore flast c (extendStore b σ) ≡ extendStore c σ
alloc-set-same = update-fresh

-- Reading the newly allocated cell returns its initial value.
alloc-get-same : ∀ {n} b (σ : Fin n → Bool) →
  lookupStore flast (extendStore b σ) ≡ b
alloc-get-same = extendStore-fresh

-- Allocation commutes with updating an existing cell.
alloc-set-distinct : ∀ {n} (i : Fin n) b c (σ : Fin n → Bool) →
  updateStore (weakenRef ≤-sucℕ i) c (extendStore b σ) ≡
  extendStore b (updateStore i c σ)
alloc-set-distinct i b c σ =
  cong (λ j → updateStore j c (extendStore b σ)) (weakenRef-suc i)
  ∙ extendStore-update i b c σ

-- Allocation commutes with reading an existing cell.
alloc-get-distinct : ∀ {n} (i : Fin n) b (σ : Fin n → Bool) →
  lookupStore (weakenRef ≤-sucℕ i) (extendStore b σ) ≡
  lookupStore i σ
alloc-get-distinct i b σ =
  cong (λ j → lookupStore j (extendStore b σ)) (weakenRef-suc i)
  ∙ extendStore-old b σ i

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
  suc m , ≤-sucℕ , flast , extendStore b σ
alloc .N-hom f = refl

-- Unlike the global-state and get/set interaction laws proved above, the
-- usual block laws do not all hold for this concrete world presentation.
-- Discarding a fresh cell is observable in the result world, and exchanging
-- two allocations is not an equality because worlds have no permutations.
-- The indexed block law is not expressible with this single-cell `alloc`.

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
    (suc m) ≤-refl (extendStore b σ))
allocOpNT A .N-hom f =
  funExt λ (b , k) → funExt₃ λ m q σ →
    cong
      (λ r → lowerAllocResult A m
        (k .PshHom.N-ob (suc m) (r , flast)
          (suc m) ≤-refl (extendStore b σ)))
      (isProp≤ _ _)

