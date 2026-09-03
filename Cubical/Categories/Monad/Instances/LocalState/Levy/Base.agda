open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet ; isSet→)
open import Cubical.Functions.FunExtEquiv using (funExt₃)

import Cubical.Data.Equality as Eq
open import Cubical.Data.Fin
  using (Fin ; discreteFin ; elimFin ; flast ; isSetFin)
open import Cubical.Data.Nat using (ℕ ; suc ; isSetℕ)
open import Cubical.Data.Nat.Order
  using (_≤_ ; ≤-refl ; ≤-trans ; <≤-trans ; ≤-sucℕ ; isProp≤)
open import Cubical.Data.Nat.Order.Inductive using (<→<ᵗ ; <ᵗ→< ; isProp<ᵗ)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Relation.Nullary using (decRec)

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Monad using (MonadFromAdjunction)
open import Cubical.Categories.Functor
open import Cubical.Categories.Monad.Base using (Monad ; IsMonad)
open import Cubical.Categories.Functors.Constant using (Constant)
open import Cubical.Categories.Instances.Discrete.More
  using (EqDiscreteCategory ; EqDiscFunc)
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Instances.Thin using (ThinCategory)
open import Cubical.Categories.NaturalTransformation
import Cubical.Categories.Enriched.Instances.Presheaf.Self as PshSelf
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
  using (-×Psh_ ; _×Psh_ ; _×PshHom_ ; π₁)
open import Cubical.Categories.Presheaf.Constructions.Exponential
  using (_⇒PshLarge_ ; appPshHom ; λPshHom)
import Cubical.Categories.Presheaf.KanExtension.Discrete as DiscreteKan
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex using (reindPshF)

module Cubical.Categories.Monad.Instances.LocalState.Levy.Base
  (V : hSet ℓ-zero) where

open Category
open Functor
open NatTrans
open PshHom
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
-- Store operations
------------------------------------------------------------------------

lookupStore : ∀ {n} → Fin n → (Fin n → V .fst) → V .fst
lookupStore i σ = σ i

updateStore : ∀ {n} → Fin n → V .fst → (Fin n → V .fst) → Fin n → V .fst
updateStore {n} i b σ j =
  decRec (λ _ → b) (λ _ → σ j) (discreteFin {n = n} i j)

-- Extend a store by appending a new cell. The fresh location is `flast`.
extendStore : ∀ {n} → V .fst → (Fin n → V .fst) → Fin (suc n) → V .fst
extendStore {n} b σ = elimFin {m = n} b σ

------------------------------------------------------------------------
-- Reference weakening
------------------------------------------------------------------------

weakenRef-comp :
  ∀ {n m p} (f : n ≤ m) (g : m ≤ p) (i : Fin n) →
  weakenRef {n = m} {m = p} g (weakenRef {n = n} {m = m} f i) ≡
  weakenRef {n = n} {m = p} (≤-trans f g) i
weakenRef-comp {n} {m} {p} f g i =
  Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = p}) refl

------------------------------------------------------------------------
-- Pi/Sigma Kan extensions
------------------------------------------------------------------------

-- For discrete source categories, these Kan extensions compute definitionally
-- to dependent sums and products.
LanΣ : Functor (WorldFam ℓ-zero) (Comp ℓ-zero)
LanΣ = DiscreteKan.Lan ℓ-zero isSetℕ include

RanΠ : Functor (WorldFam ℓ-zero) (Val ℓ-zero)
RanΠ = DiscreteKan.Ran ℓ-zero isSetℕ includeOp

LanΣ⊣include* : LanΣ ⊣ include* ℓ-zero
LanΣ⊣include* = DiscreteKan.Lan⊣J* ℓ-zero isSetℕ include

includeOp*⊣RanΠ : includeOp* ℓ-zero ⊣ RanΠ
includeOp*⊣RanΠ = DiscreteKan.J*⊣Ran ℓ-zero isSetℕ includeOp

F : Functor (Val ℓ-zero) (Comp ℓ-zero)
F = LanΣ ∘F (-×S ∘F includeOp* ℓ-zero)

U : Functor (Comp ℓ-zero) (Val ℓ-zero)
U = (RanΠ ∘F S⇒-) ∘F include* ℓ-zero

F⊣U : F ⊣ U
F⊣U = adj'→adj F U
  (Compose.LF⊣GR
    (Compose.LF⊣GR
      (adj→adj' (includeOp* ℓ-zero) RanΠ includeOp*⊣RanΠ)
      (adj→adj' -×S S⇒- -×S⊣S⇒-))
    (adj→adj' LanΣ (include* ℓ-zero) LanΣ⊣include*))

------------------------------------------------------------------------
-- Local-state monad
------------------------------------------------------------------------

T : Functor (Val ℓ-zero) (Val ℓ-zero)
T = U ∘F F

LS : Monad (Val ℓ-zero)
LS = T , MonadFromAdjunction F U F⊣U

strength : (P A : Val ℓ-zero .ob) →
  NatTrans (P ×Psh (T .F-ob A)) (T .F-ob (P ×Psh A))
strength P A .N-ob n (x , t) m n≤m σ with t m n≤m σ
... | p , m≤p , a , τ =
  p , m≤p , (P .F-hom (≤-trans n≤m m≤p) x , a) , τ
strength P A .N-hom {x = n} {y = n'} f =
  funExt λ (x , t) → funExt₃ λ m q σ → helper x t m q σ
  where
  helper : (x : P .F-ob n .fst) (t : T .F-ob A .F-ob n .fst)
    (m : ℕ) (q : n' ≤ m) (σ : Fin m → V .fst) →
    strength P A .N-ob n'
      (P .F-hom f x , T .F-ob A .F-hom f t) m q σ ≡
    T .F-ob (P ×Psh A) .F-hom f
      (strength P A .N-ob n (x , t)) m q σ
  helper x t m q σ with t m (≤-trans f q) σ
  ... | p , m≤p , a , τ =
    ΣPathP
      (refl , ΣPathP
        (isProp≤ _ _ , ΣPathP
          (cong (λ z → z , a)
            (sym
              (cong (λ r → P .F-hom r x) (isProp≤ _ _)
              ∙ funExt⁻ (P .F-seq f (≤-trans q m≤p)) x))
          , refl)))

bindT : {A B : Val ℓ-zero .ob} →
  NatTrans
    ((T .F-ob A) ×Psh (A ⇒PshLarge (T .F-ob B)))
    (T .F-ob B)
bindT {A} {B} =
  seqTrans (PshSelf.swap (World ^op) ℓ-zero)
    (seqTrans (strength (A ⇒PshLarge (T .F-ob B)) A)
      (IsMonad.bind (LS .snd) .N-ob
        ((A ⇒PshLarge (T .F-ob B)) ×Psh A , B)
        (PshHom→NatTrans (appPshHom A (T .F-ob B)))))

------------------------------------------------------------------------
-- Algebraic operations
------------------------------------------------------------------------

getM : NatTrans Ref (T .F-ob VVal)
getM .N-ob n i m n≤m σ =
  m , ≤-refl ,
    lookupStore {n = m} (weakenRef {n = n} {m = m} n≤m i) σ , σ
getM .N-hom {x = n} {y = n'} f =
  funExt λ (i : Fin n) →
  funExt₃ λ (m : ℕ) (q : n' ≤ m) (σ : Fin m → V .fst) →
    cong
      {B = λ _ →
        Σ[ p ∈ ℕ ] (m ≤ p) ×
          (VVal .F-ob p .fst × (Fin p → V .fst))}
      (λ (j : Fin m) → m , ≤-refl , lookupStore {n = m} j σ , σ)
      (weakenRef-comp {n = n} {m = n'} {p = m} f q i)

setM : NatTrans (Ref ×Psh VVal) (T .F-ob UnitVal)
setM .N-ob n (i , b) m n≤m σ =
  m , ≤-refl , tt ,
    updateStore {n = m} (weakenRef {n = n} {m = m} n≤m i) b σ
setM .N-hom {x = n} {y = n'} f =
  funExt λ (i , b) →
  funExt₃ λ (m : ℕ) (q : n' ≤ m) (σ : Fin m → V .fst) →
    cong
      {B = λ _ →
        Σ[ p ∈ ℕ ] (m ≤ p) ×
          (UnitVal .F-ob p .fst × (Fin p → V .fst))}
      (λ j → m , ≤-refl , tt , updateStore {n = m} j b σ)
      (weakenRef-comp {n = n} {m = n'} {p = m} f q i)

allocM : NatTrans VVal (T .F-ob Ref)
allocM .N-ob n b m n≤m σ =
  suc m , ≤-sucℕ , flast {k = m} , extendStore {n = m} b σ
allocM .N-hom _ = refl

get : (A : Val ℓ-zero .ob) →
  NatTrans (Ref ×Psh (VVal ⇒PshLarge (T .F-ob A))) (T .F-ob A)
get A =
  seqTrans
    (PshHom→NatTrans
      (NatTrans→PshHom getM ×PshHom idPshHom))
    (bindT {VVal} {A})

set : (A : Val ℓ-zero .ob) →
  NatTrans ((Ref ×Psh VVal) ×Psh (T .F-ob A)) (T .F-ob A)
set A =
  seqTrans
    (PshHom→NatTrans
      (NatTrans→PshHom setM ×PshHom
        λPshHom UnitVal (T .F-ob A) (π₁ (T .F-ob A) UnitVal)))
    (bindT {UnitVal} {A})

alloc : (A : Val ℓ-zero .ob) →
  NatTrans (VVal ×Psh (Ref ⇒PshLarge (T .F-ob A))) (T .F-ob A)
alloc A =
  seqTrans
    (PshHom→NatTrans
      (NatTrans→PshHom allocM ×PshHom idPshHom))
    (bindT {Ref} {A})
