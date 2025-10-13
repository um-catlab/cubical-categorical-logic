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
open import Cubical.Categories.Constructions.FullSubcategory.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Categoryᴰ
open FullSubcategory'

isFinite : hSet ℓ → Type ℓ
isFinite X = isFinOrd ⟨ X ⟩

FINORD : ∀ ℓ → Category _ ℓ
FINORD ℓ = FullSubcategory' (SET ℓ) isFinite

open Category

⟨_⟩fo : FINORD ℓ .ob → Σ (Type ℓ) isFinOrd
⟨ A ⟩fo = (A .fst .fst) , (A .snd)

mkfo : (A : Type ℓ) → isFinOrd A → FINORD ℓ .ob
mkfo A isFinOrdA = (A , isFinSet→isSet (isFinOrd→isFinSet isFinOrdA)) , isFinOrdA

FINORD^op : ∀ ℓ → Category _ ℓ
FINORD^op ℓ = (FINORD ℓ) ^op
