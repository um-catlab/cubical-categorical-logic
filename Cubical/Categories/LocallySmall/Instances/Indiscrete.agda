module Cubical.Categories.LocallySmall.Instances.Indiscrete where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Category.HLevels
open import Cubical.Categories.LocallySmall.Variables

open Category

Indiscrete : (ob : Typeω) → GloballySmallCategory ob ℓ-zero
Indiscrete ob .Hom[_,_] = λ _ _ → Unit
Indiscrete ob .id = tt
Indiscrete ob ._⋆_ = λ f g → tt
Indiscrete ob .⋆IdL = λ _ → refl
Indiscrete ob .⋆IdR = λ _ → refl
Indiscrete ob .⋆Assoc = λ _ _ _ → refl
Indiscrete ob .isSetHom = isSetUnit

IndiscreteHasContrHoms : ∀ {ob} → hasContrHoms (Indiscrete ob)
IndiscreteHasContrHoms c c' = isContrUnit

module _ {ob : Typeω} (c c' : ob) where
  mkIndiscreteIso : CatIso (Indiscrete ob) c c'
  mkIndiscreteIso = mkContrHomsIso (Indiscrete ob) IndiscreteHasContrHoms c c'
