{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Monad.Instances.LocalState.Levy.Kan where

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

open Category
open Functor
open NatTrans
open UnitCounit

open import Cubical.Categories.Monad.Instances.LocalState.Levy.Base

-- General presentation using the library's coend and end Kan extensions.
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
  [ (suc m , ≤-sucℕ , (flast , extendStore b σ)) ]
alloc .N-ob n b .Outer.End.coh Eq.refl n≤m = refl
alloc .N-hom f =
  funExt λ b → Outer.end≡ _ λ m q → funExt λ σ → refl
