{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Base.HLevel1Homs

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' : Level

open Category
open Categoryᴰ
-- Terminal category over a base category
Unitᴰ : (C : Category ℓC ℓC') → Categoryᴰ C ℓ-zero ℓ-zero
Unitᴰ C .ob[_] x = Unit
Unitᴰ C .Hom[_][_,_] f tt tt = Unit
Unitᴰ C .idᴰ = tt
Unitᴰ C ._⋆ᴰ_ = λ _ _ → tt
Unitᴰ C .⋆IdLᴰ fᴰ i = tt
Unitᴰ C .⋆IdRᴰ fᴰ i = tt
Unitᴰ C .⋆Assocᴰ fᴰ gᴰ hᴰ i = tt
Unitᴰ C .isSetHomᴰ x y x₁ y₁ i i₁ = tt

hasContrHomsUnitᴰ : {C : Category ℓC ℓC'} → hasContrHoms (Unitᴰ C)
hasContrHomsUnitᴰ f cᴰ cᴰ' = isContrUnit

module _ {C : Category ℓC ℓC'}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {D : Category ℓD ℓD'}
         where

  -- TODO: this should be an instance of FullSubcategory.intro
  intro : (F : Functor C D) → Functorᴰ F Cᴰ (Unitᴰ D)
  intro F .Functorᴰ.F-obᴰ = λ _ → tt
  intro F .Functorᴰ.F-homᴰ = λ _ → tt
  intro F .Functorᴰ.F-idᴰ = refl
  intro F .Functorᴰ.F-seqᴰ fᴰ gᴰ = refl

-- Terminal category over the terminal category
UnitCᴰ : Categoryᴰ (TerminalCategory {ℓ-zero}) ℓ-zero ℓ-zero
UnitCᴰ = Unitᴰ TerminalCategory

