module Cubical.Categories.LocallySmall.Instances.Indiscrete where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables

open Category
open Σω

Indiscrete : (ob : Typeω) → GloballySmallCategory ob ℓ-zero
Indiscrete ob .Hom[_,_] = λ _ _ → Unit
Indiscrete ob .id = tt
Indiscrete ob ._⋆_ = λ f g → tt
Indiscrete ob .⋆IdL = λ _ → refl
Indiscrete ob .⋆IdR = λ _ → refl
Indiscrete ob .⋆Assoc = λ _ _ _ → refl
Indiscrete ob .isSetHom = isSetUnit
