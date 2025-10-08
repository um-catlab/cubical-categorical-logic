module Cubical.Categories.Instances.FinSets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit
open import Cubical.Data.FinSet

open import Cubical.Categories.Category renaming (pathToIso to catPathToIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Categoryᴰ

isFinite : Categoryᴰ (SET ℓ) ℓ ℓ-zero
isFinite .ob[_] X = isFinSet ⟨ X ⟩
isFinite .Hom[_][_,_] _ _ _ = Unit
isFinite .idᴰ = _
isFinite ._⋆ᴰ_ = _
isFinite .⋆IdLᴰ _ = refl
isFinite .⋆IdRᴰ _ = refl
isFinite .⋆Assocᴰ _ _ _ = refl
isFinite .isSetHomᴰ = isSetUnit

FINSET : Category _ ℓ
FINSET = ∫C isFinite
