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
isFinite X = isFinSet ⟨ X ⟩

FINSET : ∀ ℓ → Category _ ℓ
FINSET ℓ = FullSubcategory' (SET ℓ) isFinite

open Category

⟨_⟩fs : FINSET ℓ .ob → FinSet ℓ
⟨ A ⟩fs = (A .fst .fst) , (A .snd)

mkfs : (A : Type ℓ) → isFinSet A → FINSET ℓ .ob
mkfs A isFinSetA = (A , isFinSet→isSet isFinSetA) , isFinSetA

FINSET^op : ∀ ℓ → Category _ ℓ
FINSET^op ℓ = (FINSET ℓ) ^op
