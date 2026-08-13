{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Monad.Instances.LocalState.Levy.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool hiding (_≤_ ; isProp≤)
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Monad
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Instances.Discrete.More
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Thin
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.CCC
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct.LocalRepresentability
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.KanExtension
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Profunctor.General

open Category
open Functor
open NatTrans
open UnitCounit

World : Category ℓ-zero ℓ-zero
World = ThinCategory ℕ _≤_ ≤-refl ≤-trans isProp≤

|World| : Category ℓ-zero ℓ-zero
|World| = InductiveDiscreteCategory ℕ isSetℕ

-- The identity-on-objects inclusions into future- and past-directed worlds.
include : Functor |World| World
include = InductiveDiscFunc (λ n → n)

includeOp : Functor |World| (World ^op)
includeOp = InductiveDiscFunc (λ n → n)

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

Lan-include⊣include* :
  Lan.Lan ℓ-zero include ⊣ include* ℓ-zero
Lan-include⊣include* = Lan.adj ℓ-zero include

includeOp*⊣Ran-includeOp :
  includeOp* ℓ-zero ⊣ Ran.Ran ℓ-zero includeOp
includeOp*⊣Ran-includeOp = Ran.adj ℓ-zero includeOp

S : WorldFam ℓ-zero .ob
S .F-ob n .fst = Fin n → Bool
S .F-ob n .snd = isSet→ isSetBool
S .F-hom Eq.refl = λ σ → σ
S .F-id = refl
S .F-seq Eq.refl Eq.refl = refl

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

-- Levy's CBPV adjunction, factored through discrete world-indexed families.
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
