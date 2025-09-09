{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.Lift where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓP ℓQ ℓS : Level

LiftPsh : ∀ {C : Category ℓ ℓ'} (P : Presheaf C ℓA) (ℓ'' : Level) → Presheaf C (ℓ-max ℓA ℓ'')
LiftPsh P ℓ'' = LiftF {ℓ' = ℓ''} ∘F P
