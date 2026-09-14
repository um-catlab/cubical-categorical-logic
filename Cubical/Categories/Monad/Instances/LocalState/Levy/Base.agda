{-
Levy's local-state monad

The composing adjunctions:

       Free World                -×S              PSH→Fam (World ^op)
     ←──────────────          ←────────          ←─────────────────────
Comp        ⊥        WorldFam     ⊥     WorldFam           ⊥            Val
     ──────────────→          ────────→          ─────────────────────→
      PSH→Fam World              S⇒-               Cofree (World ^op)

The upper, leftward adjoints compose to F : Val → Comp; the lower,
rightward adjoints compose to U : Comp → Val. Thus F ⊣ U and T = U ∘F F.
Here World = (ℕ, ≤), Val = [World, Set], Comp = [Worldᵒᵖ, Set],
and WorldFam is the category of ℕ-indexed families of sets.

Writing S n = Fin n → |V| and A n for the underlying set at n:

  T A n = (m : ℕ) → n ≤ m → S m →
            Σ[ p ∈ ℕ ] (m ≤ p) × (A p × S p).

A computation at n accepts a store in any future world m ≥ n, then
returns a value and store in a possibly larger world p ≥ m.
At world n : ℕ, the primitive operations are the following functions:

  getMₙ : Fin n → T VVal n
  getMₙ (i : Fin n) (m : ℕ) (q : n ≤ m) (σ : S m) =
    (m , ≤-refl , σ (weakenRef q i) , σ)

  setMₙ : Fin n × |V| → T UnitVal n
  setMₙ ((i , b) : Fin n × |V|) (m : ℕ) (q : n ≤ m) (σ : S m) =
    (m , ≤-refl , tt , updateStore (weakenRef q i) b σ)

  allocMₙ : |V| → T Ref n
  allocMₙ (b : |V|) (m : ℕ) (q : n ≤ m) (σ : S m) =
    (suc m , ≤-sucℕ , flast , extendStore b σ)

updateStore changes one cell; extendStore appends a
cell initialized with b, whose fresh reference is flast.

Based on Paul Blain Levy's possible-world model for cell generation:
Call-By-Push-Value, PhD thesis (2001), Chapter 7; see also Section 6.6
onwards of the book Call-By-Push-Value: A Functional/Imperative Synthesis.
https://pblevy.github.io/papers/thesisqmwphd.pdf
https://doi.org/10.1007/978-94-007-0954-6_6
Here worlds are natural numbers and every cell stores an element of V.
-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hSet ; isSet→ ; isSet×)
open import Cubical.Functions.FunExtEquiv using (funExt₃)

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
open import Cubical.Categories.Instances.Sets using (SET)
open import Cubical.Categories.Instances.Thin using (ThinCategory)
import Cubical.Categories.NaturalTransformation as NT
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
  using (_×Psh_)
import Cubical.Categories.Presheaf.Family.Base as Family
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
  using (_⇒PshLargeStrict_ ; appPshHomStrict ; λPshHomStrict ;
    _×PshHomStrict_ ; ×PshIntroStrict ; π₁ ; π₂)

module Cubical.Categories.Monad.Instances.LocalState.Levy.Base
  (V : hSet ℓ-zero) where

open Category
open Functor
open PshHomStrict
open UnitCounit

------------------------------------------------------------------------
-- Worlds and presheaf categories
------------------------------------------------------------------------

World : Category ℓ-zero ℓ-zero
World = ThinCategory ℕ _≤_ ≤-refl ≤-trans isProp≤

Val : Category (ℓ-suc ℓ-zero) ℓ-zero
Val = PRESHEAF (World ^op) ℓ-zero

Comp : Category (ℓ-suc ℓ-zero) ℓ-zero
Comp = PRESHEAF World ℓ-zero

WorldFam : Category (ℓ-suc ℓ-zero) ℓ-zero
WorldFam = Family.Families World ℓ-zero

S : WorldFam .ob
S n = (Fin n → V .fst) , isSet→ (V .snd)

VVal : Val .ob
VVal = Constant ((World ^op) ^op) (SET ℓ-zero) V

UnitVal : Val .ob
UnitVal = Constant ((World ^op) ^op) (SET ℓ-zero) (Unit , isSetUnit)

weakenRef : ∀ {n m} → n ≤ m → Fin n → Fin m
weakenRef {n} {m} n≤m (i , i<n) =
  i , <→<ᵗ (<≤-trans (<ᵗ→< i<n) n≤m)

Ref : Val .ob
Ref .F-ob n = Fin n , isSetFin {k = n}
Ref .F-hom {x = n} {y = m} f = weakenRef {n = n} {m = m} f
Ref .F-id {x = n} =
  funExt λ (_ : Fin n) →
    Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = n}) refl
Ref .F-seq {x = n} {y = m} {z = p} f g =
  funExt λ (_ : Fin n) →
    Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = p}) refl

-×S : Functor WorldFam WorldFam
-×S .F-ob A n = (A n .fst × S n .fst) , isSet× (A n .snd) (S n .snd)
-×S .F-hom α n (a , σ) = α n a , σ
-×S .F-id = refl
-×S .F-seq α β = refl

S⇒- : Functor WorldFam WorldFam
S⇒- .F-ob A n = (S n .fst → A n .fst) , isSet→ (A n .snd)
S⇒- .F-hom α n k σ = α n (k σ)
S⇒- .F-id = refl
S⇒- .F-seq α β = refl

-×S⊣S⇒- : -×S ⊣ S⇒-
-×S⊣S⇒- ._⊣_.η .NT.NatTrans.N-ob A n a σ = a , σ
-×S⊣S⇒- ._⊣_.η .NT.NatTrans.N-hom α = refl
-×S⊣S⇒- ._⊣_.ε .NT.NatTrans.N-ob A n (k , σ) = k σ
-×S⊣S⇒- ._⊣_.ε .NT.NatTrans.N-hom α = refl
-×S⊣S⇒- ._⊣_.triangleIdentities .TriangleIdentities.Δ₁ A = refl
-×S⊣S⇒- ._⊣_.triangleIdentities .TriangleIdentities.Δ₂ A = refl

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
-- Presheaves and families adjunctions
------------------------------------------------------------------------

-- Free World X n = Σ[ m ∈ ℕ ] (n ≤ m) × X m.
-- Cofree (World ^op) X n = (m : ℕ) → n ≤ m → X m.

F : Functor Val Comp
F = Family.Free World isSetℕ ∘F (-×S ∘F Family.PSH→Fam (World ^op))

U : Functor Comp Val
U = (Family.Cofree (World ^op) ∘F S⇒-) ∘F Family.PSH→Fam World

F⊣U : F ⊣ U
F⊣U = adj'→adj F U
  (Compose.LF⊣GR
    (Compose.LF⊣GR
      (adj→adj' (Family.PSH→Fam (World ^op)) (Family.Cofree (World ^op))
        (Family.CofreeFamAdj (World ^op)))
      (adj→adj' -×S S⇒- -×S⊣S⇒-))
    (adj→adj' (Family.Free World isSetℕ) (Family.PSH→Fam World)
      (Family.FreeFamAdj World isSetℕ)))

------------------------------------------------------------------------
-- Local-state monad
------------------------------------------------------------------------

T : Functor Val Val
T = U ∘F F

LS : Monad Val
LS = T , MonadFromAdjunction F U F⊣U

strength : (P A : Val .ob) →
  Val [ P ×Psh (T .F-ob A) , T .F-ob (P ×Psh A) ]
strength P A .N-ob n (x , t) m n≤m σ with t m n≤m σ
... | p , m≤p , a , τ =
  p , m≤p , (P .F-hom (≤-trans n≤m m≤p) x , a) , τ
strength P A .N-hom n' n f (x , t) z e =
  sym (funExt₃ (helper x t)) ∙ cong (strength P A .N-ob n') e
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

private
  -- Elaborate the component projection with an abstract functor. Projecting
  -- directly at T makes Agda normalize the large presheaf monad interface.
  μ-at : (M : Functor Val Val) → IsMonad M →
    (B : Val .ob) →
    Val [ M .F-ob (M .F-ob B) , M .F-ob B ]
  μ-at M mon B = IsMonad.μ mon .NT.NatTrans.N-ob B

bindT : {A B : Val .ob} →
  Val [
    (T .F-ob A) ×Psh (A ⇒PshLargeStrict (T .F-ob B)) ,
    T .F-ob B ]
bindT {A} {B} =
  swap ⋆PshHomStrict strength K A ⋆PshHomStrict applyK
  where
  K : Val .ob
  K = A ⇒PshLargeStrict (T .F-ob B)

  swap : Val [ (T .F-ob A) ×Psh K , K ×Psh (T .F-ob A) ]
  swap = ×PshIntroStrict (π₂ (T .F-ob A) K) (π₁ (T .F-ob A) K)

  ev : Val [ K ×Psh A , T .F-ob B ]
  ev = appPshHomStrict A (T .F-ob B)

  liftEv : Val [ T .F-ob (K ×Psh A) , T .F-ob (T .F-ob B) ]
  liftEv = T .F-hom ev

  μB : Val [ T .F-ob (T .F-ob B) , T .F-ob B ]
  μB = μ-at T (LS .snd) B

  applyK : Val [ T .F-ob (K ×Psh A) , T .F-ob B ]
  applyK = liftEv ⋆PshHomStrict μB

------------------------------------------------------------------------
-- Algebraic operations
------------------------------------------------------------------------

getM : Val [ Ref , T .F-ob VVal ]
getM .N-ob n i m n≤m σ =
  m , ≤-refl ,
    lookupStore {n = m} (weakenRef {n = n} {m = m} n≤m i) σ , σ
getM .N-hom n' n f i j e =
  funExt₃ λ (m : ℕ) (q : n' ≤ m) (σ : Fin m → V .fst) →
    cong
      {B = λ _ →
        Σ[ p ∈ ℕ ] (m ≤ p) ×
          (VVal .F-ob p .fst × (Fin p → V .fst))}
      (λ (j : Fin m) → m , ≤-refl , lookupStore {n = m} j σ , σ)
      (sym (weakenRef-comp {n = n} {m = n'} {p = m} f q i)
        ∙ cong (weakenRef {n = n'} {m = m} q) e)

setM : Val [ Ref ×Psh VVal , T .F-ob UnitVal ]
setM .N-ob n (i , b) m n≤m σ =
  m , ≤-refl , tt ,
    updateStore {n = m} (weakenRef {n = n} {m = m} n≤m i) b σ
setM .N-hom n' n f (i , b) (j , c) e =
  funExt₃ λ (m : ℕ) (q : n' ≤ m) (σ : Fin m → V .fst) →
    cong₂
      {C = λ _ _ →
        Σ[ p ∈ ℕ ] (m ≤ p) ×
          (UnitVal .F-ob p .fst × (Fin p → V .fst))}
      (λ j c → m , ≤-refl , tt , updateStore {n = m} j c σ)
      (sym (weakenRef-comp {n = n} {m = n'} {p = m} f q i)
        ∙ cong (weakenRef {n = n'} {m = m} q) (cong fst e))
      (cong snd e)

allocM : Val [ VVal , T .F-ob Ref ]
allocM .N-ob n b m n≤m σ =
  suc m , ≤-sucℕ , flast {k = m} , extendStore {n = m} b σ
allocM .N-hom n' n f b c e =
  funExt₃ λ m q σ →
    cong (λ d → suc m , ≤-sucℕ , flast {k = m} , extendStore {n = m} d σ) e

get : (A : Val .ob) →
  Val [ Ref ×Psh (VVal ⇒PshLargeStrict (T .F-ob A)) , T .F-ob A ]
get A =
  (getM ×PshHomStrict idPshHomStrict) ⋆PshHomStrict bindT {VVal} {A}

set : (A : Val .ob) →
  Val [ (Ref ×Psh VVal) ×Psh (T .F-ob A) , T .F-ob A ]
set A =
  (setM ×PshHomStrict
    λPshHomStrict UnitVal (T .F-ob A) (π₁ (T .F-ob A) UnitVal))
  ⋆PshHomStrict bindT {UnitVal} {A}

alloc : (A : Val .ob) →
  Val [ VVal ×Psh (Ref ⇒PshLargeStrict (T .F-ob A)) , T .F-ob A ]
alloc A =
  (allocM ×PshHomStrict idPshHomStrict) ⋆PshHomStrict bindT {Ref} {A}
