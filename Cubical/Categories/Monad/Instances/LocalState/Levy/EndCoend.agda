module Cubical.Categories.Monad.Instances.LocalState.Levy.EndCoend where

open import Cubical.Foundations.Prelude

import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive using (isProp<ᵗ)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.SetQuotients

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Monad using (MonadFromAdjunction)
open import Cubical.Categories.Functor
open import Cubical.Categories.Monad.Base using (Monad)
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base using (_×Psh_)
open import Cubical.Categories.Presheaf.KanExtension
open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base

open Category
open Functor
open NatTrans
open UnitCounit

------------------------------------------------------------------------
-- End/coend presentation of the Kan extensions
------------------------------------------------------------------------

-- The same Kan-extension construction as PiSigma, presented through the
-- library's coend and end definitions rather than definitionally as Σ and Π.
Lan-include⊣include* :
  Lan.Lan ℓ-zero include ⊣ include* ℓ-zero
Lan-include⊣include* = Lan.adj ℓ-zero include

includeOp*⊣Ran-includeOp :
  includeOp* ℓ-zero ⊣ Ran.Ran ℓ-zero includeOp
includeOp*⊣Ran-includeOp = Ran.adj ℓ-zero includeOp

F : Functor (Val ℓ-zero) (Comp ℓ-zero)
F = Lan.Lan ℓ-zero include ∘F (-×S ∘F includeOp* ℓ-zero)

U : Functor (Comp ℓ-zero) (Val ℓ-zero)
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

------------------------------------------------------------------------
-- Local-state monad
------------------------------------------------------------------------

T : Functor (Val ℓ-zero) (Val ℓ-zero)
T = U ∘F F

LS : Monad (Val ℓ-zero)
LS = T , MonadFromAdjunction F U F⊣U

module Outer = Ran ℓ-zero includeOp
module Inner = Lan ℓ-zero include

now : (A : Val ℓ-zero .ob) (n : ℕ) →
  A .F-ob n .fst → S .F-ob n .fst →
  Inner.Quo ((-×S ∘F includeOp* ℓ-zero) .F-ob A) n
now A n a σ = [ (n , ≤-refl , (a , σ)) ]

------------------------------------------------------------------------
-- Algebraic operations
------------------------------------------------------------------------

private
  get-now : (n : ℕ) → Fin n → (m : ℕ) → n ≤ m →
    (Fin m → Bool) →
    Inner.Quo ((-×S ∘F includeOp* ℓ-zero) .F-ob BoolVal) m
  get-now n i m n≤m σ =
    now BoolVal m
      (lookupStore {n = m} (weakenRef {n = n} {m = m} n≤m i) σ) σ

  set-now : (n : ℕ) → Fin n × Bool → (m : ℕ) → n ≤ m →
    (Fin m → Bool) →
    Inner.Quo ((-×S ∘F includeOp* ℓ-zero) .F-ob UnitVal) m
  set-now n (i , b) m n≤m σ =
    now UnitVal m tt
      (updateStore {n = m} (weakenRef {n = n} {m = m} n≤m i) b σ)

  alloc-now : (n : ℕ) → Bool → (m : ℕ) → n ≤ m →
    (Fin m → Bool) →
    Inner.Quo ((-×S ∘F includeOp* ℓ-zero) .F-ob Ref) m
  alloc-now n b m n≤m σ =
    [ (suc m , ≤-sucℕ ,
        (flast {k = m} , extendStore {n = m} b σ)) ]

get : NatTrans Ref (T .F-ob BoolVal)
get .N-ob n i .Outer.End.fun m n≤m σ = get-now n i m n≤m σ
get .N-ob n i .Outer.End.coh {c = m} Eq.refl n≤m =
  funExt λ (σ : Fin m → Bool) →
    cong (λ (j : Fin m) →
      now BoolVal m (lookupStore {n = m} j σ) σ)
      (Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = m}) refl)
get .N-hom {x = n} {y = n'} f =
  funExt λ (i : Fin n) →
    Outer.end≡ _ λ (m : ℕ) (q : n' ≤ m) →
      funExt λ (σ : Fin m → Bool) →
        cong (λ j → now BoolVal m (lookupStore {n = m} j σ) σ)
          (weakenRef-comp {n = n} {m = n'} {p = m} f q i)

set : NatTrans (Ref ×Psh BoolVal) (T .F-ob UnitVal)
set .N-ob n x .Outer.End.fun m n≤m σ = set-now n x m n≤m σ
set .N-ob n (i , b) .Outer.End.coh {c = m} Eq.refl n≤m =
  let
    ref-coh :
      weakenRef
        (seq' (World ^op) (includeOp ⟪ Eq.refl ⟫) n≤m) i
      ≡ weakenRef n≤m i
    ref-coh = Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = m}) refl
  in funExt λ (σ : Fin m → Bool) →
    cong (λ (j : Fin m) →
      now UnitVal m tt (updateStore {n = m} j b σ)) ref-coh
set .N-hom {x = n} {y = n'} f =
  funExt λ ((i , b) : Fin n × Bool) →
    Outer.end≡ _ λ (m : ℕ) (q : n' ≤ m) →
      funExt λ (σ : Fin m → Bool) →
        cong (λ j → now UnitVal m tt (updateStore {n = m} j b σ))
          (weakenRef-comp {n = n} {m = n'} {p = m} f q i)

alloc : NatTrans BoolVal (T .F-ob Ref)
alloc .N-ob n b .Outer.End.fun m n≤m σ = alloc-now n b m n≤m σ
alloc .N-ob n b .Outer.End.coh Eq.refl n≤m = refl
alloc .N-hom f =
  funExt λ b → Outer.end≡ _ λ m q → funExt λ σ → refl
