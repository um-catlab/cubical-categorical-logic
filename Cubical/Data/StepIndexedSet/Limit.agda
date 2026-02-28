{-

  Forgetful functor from ω+Sets to Sets, projecting the limit
  component Xω.

  This functor has a left adjoint: the "constant" ω+Type
  construction, which sends a set S to the ω+Type with Xᵢ = S,
  πᵢ = id, Xω = S.

-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Data.StepIndexedSet.Limit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.StepIndexedSet

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Instances.Sets

open Category
open Functor
open ω+Type
open ω+Hom
open ωType
open ωHom
open ωChain

private
  variable
    ℓ : Level

-- ωChains over a set-valued ωType form a set
isSetωChain : {X : ωType ℓ} → isωSet X → isSet (ωChain X)
isSetωChain {X = X} Xset =
  isOfHLevelRetractFromIso 2
    (ωChainΣIso {X = ωChainω+Type X} {Y = ωChainω+Type X})
    (isSetΣ (isSetΠ λ i → Xset i)
      λ xᵢ → isProp→isSet
        (isPropΠ λ i → Xset i _ _))

-- Xω is a set whenever the finite levels are
isSetXω : (X : ω+Type ℓ) → isωSet (X .Xfin) → isSet (X .Xω)
isSetXω X Xset =
  isOfHLevelRespectEquiv 2
    (invEquiv (X .π , X .isLimit))
    (isSetωChain Xset)

-- Forgetful functor projecting out Xω
Lim : Functor (ω+SET ℓ) (SET ℓ)
Lim .F-ob (X , Xset) = X .Xω , isSetXω X Xset
Lim .F-hom f = f .fω
Lim .F-id = refl
Lim .F-seq f g = refl

-- Constant ω+Type: every level is S, all maps are id
constωType : Type ℓ → ωType ℓ
constωType S .Xᵢ _ = S
constωType S .πᵢ _ s = s

constω+Type : (S : Type ℓ) → isSet S → ω+Type ℓ
constω+Type S Sset .Xfin = constωType S
constω+Type S Sset .Xω = S
constω+Type S Sset .π s .xᵢ _ = s
constω+Type S Sset .π s .xᵢ-nat _ = refl
constω+Type S Sset .isLimit = isoToIsEquiv theIso
  where
    allEq : (c : ωChain (constωType S))
      → ∀ i → c .xᵢ 0 ≡ c .xᵢ i
    allEq c zero = refl
    allEq c (suc n) =
      allEq c n ∙ sym (c .xᵢ-nat n)

    theIso : Iso S (ωChain (constωType S))
    theIso .Iso.fun s .xᵢ _ = s
    theIso .Iso.fun s .xᵢ-nat _ = refl
    theIso .Iso.inv c = c .xᵢ 0
    theIso .Iso.ret s = refl
    theIso .Iso.sec c i .xᵢ j = allEq c j i
    theIso .Iso.sec c i .xᵢ-nat j =
      isProp→PathP
        (λ i → Sset
          (allEq c (suc j) i) (allEq c j i))
        refl (c .xᵢ-nat j) i

-- Constant ω+Hom: apply f at every level
constω+Hom : {S : Type ℓ} {Sset : isSet S}
  {Y : ω+Type ℓ}
  → (S → Y .Xω) → ω+Hom (constω+Type S Sset) Y
constω+Hom {Y = Y} f .fFin .fᵢ i s =
  Y .π (f s) .xᵢ i
constω+Hom {Y = Y} f .fFin .fᵢ-nat n s =
  Y .π (f s) .xᵢ-nat n
constω+Hom f .fω = f
constω+Hom {Y = Y} f .fω-nat i s = refl

-- Left adjoint: CONST ⊣ Lim
CONST : LeftAdjoint (Lim {ℓ})
CONST (S , Sset) .UniversalElement.vertex .fst =
  constω+Type S Sset
CONST (S , Sset) .UniversalElement.vertex .snd
  _ = Sset
CONST (S , Sset) .UniversalElement.element s = s
CONST (S , Sset) .UniversalElement.universal
  (Y , Yset) = isIsoToIsEquiv
    ( constω+Hom
    , (λ g → refl)
    , (λ f → makeω+HomPath Yset
        (funExt λ i → funExt λ s →
          f .fω-nat i s)))
