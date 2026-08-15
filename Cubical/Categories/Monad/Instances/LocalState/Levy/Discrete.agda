-- {-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Monad.Instances.LocalState.Levy.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Functions.FunExtEquiv using (funExt₃)

open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Monad using (MonadFromAdjunction)
open import Cubical.Categories.Functor
open import Cubical.Categories.Monad.Base using (Monad ; IsMonad)
open import Cubical.Categories.NaturalTransformation
import Cubical.Categories.Enriched.Instances.Presheaf.Self as PshSelf
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
  using (_×Psh_ ; _×PshHom_ ; π₁)
open import Cubical.Categories.Presheaf.Constructions.Exponential
  using (_⇒PshLarge_ ; appPshHom ; λPshHom)
import Cubical.Categories.Presheaf.KanExtension.Discrete as DiscreteKan
open import Cubical.Categories.Presheaf.Morphism.Alt

open Category
open Functor
open NatTrans
open PshHom
open UnitCounit

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base

-- Computational presentation using dependent sums and products.
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
    (m : ℕ) (q : n' ≤ m) (σ : Fin m → Bool) →
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

getM : NatTrans Ref (T .F-ob BoolVal)
getM .N-ob n i m n≤m σ =
  m , ≤-refl ,
    lookupStore {n = m} (weakenRef {n = n} {m = m} n≤m i) σ , σ
getM .N-hom {x = n} {y = n'} f =
  funExt λ (i : Fin n) →
  funExt₃ λ (m : ℕ) (q : n' ≤ m) (σ : Fin m → Bool) →
    cong
      {B = λ _ →
        Σ[ p ∈ ℕ ] (m ≤ p) ×
          (BoolVal .F-ob p .fst × (Fin p → Bool))}
      (λ (j : Fin m) → m , ≤-refl , lookupStore {n = m} j σ , σ)
      (weakenRef-comp {n = n} {m = n'} {p = m} f q i)

setM : NatTrans (Ref ×Psh BoolVal) (T .F-ob UnitVal)
setM .N-ob n (i , b) m n≤m σ =
  m , ≤-refl , tt ,
    updateStore {n = m} (weakenRef {n = n} {m = m} n≤m i) b σ
setM .N-hom {x = n} {y = n'} f =
  funExt λ (i , b) →
  funExt₃ λ (m : ℕ) (q : n' ≤ m) (σ : Fin m → Bool) →
    cong
      {B = λ _ →
        Σ[ p ∈ ℕ ] (m ≤ p) ×
          (UnitVal .F-ob p .fst × (Fin p → Bool))}
      (λ j → m , ≤-refl , tt , updateStore {n = m} j b σ)
      (weakenRef-comp {n = n} {m = n'} {p = m} f q i)

allocM : NatTrans BoolVal (T .F-ob Ref)
allocM .N-ob n b m n≤m σ =
  suc m , ≤-sucℕ , flast {k = m} , extendStore {n = m} b σ
allocM .N-hom f = refl

get : (A : Val ℓ-zero .ob) →
  NatTrans (Ref ×Psh (BoolVal ⇒PshLarge (T .F-ob A))) (T .F-ob A)
get A =
  seqTrans
    (PshHom→NatTrans
      (NatTrans→PshHom getM ×PshHom idPshHom))
    (bindT {BoolVal} {A})

set : (A : Val ℓ-zero .ob) →
  NatTrans ((Ref ×Psh BoolVal) ×Psh (T .F-ob A)) (T .F-ob A)
set A =
  seqTrans
    (PshHom→NatTrans
      (NatTrans→PshHom setM ×PshHom
        λPshHom UnitVal (T .F-ob A) (π₁ (T .F-ob A) UnitVal)))
    (bindT {UnitVal} {A})

alloc : (A : Val ℓ-zero .ob) →
  NatTrans (BoolVal ×Psh (Ref ⇒PshLarge (T .F-ob A))) (T .F-ob A)
alloc A =
  seqTrans
    (PshHom→NatTrans
      (NatTrans→PshHom allocM ×PshHom idPshHom))
    (bindT {Ref} {A})
