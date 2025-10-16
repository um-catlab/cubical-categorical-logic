{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓP ℓQ ℓS : Level

open Functor
open PshHom

UnitPsh : ∀ {C : Category ℓ ℓ'} → Presheaf C ℓ-zero
UnitPsh = Constant _ _ (Unit , isSetUnit)

Unit*Psh : ∀ {C : Category ℓ ℓ'} {ℓ''} → Presheaf C ℓ''
Unit*Psh = Constant _ _ (Unit* , isOfHLevelLift 2 isSetUnit)

UnitPsh-intro : ∀ {C : Category ℓ ℓ'}{P : Presheaf C ℓA}
  → PshHom P UnitPsh
UnitPsh-intro .N-ob = λ x _ → tt
UnitPsh-intro .N-hom x y f p = refl

Unit*Psh-intro : ∀ {C : Category ℓ ℓ'}{P : Presheaf C ℓA}{ℓ''}
  → PshHom P (Unit*Psh {ℓ'' = ℓ''})
Unit*Psh-intro .N-ob = λ x _ → lift tt
Unit*Psh-intro .N-hom x y f p = refl
