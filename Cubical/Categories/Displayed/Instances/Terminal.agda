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
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Base.HLevel1Homs
open import Cubical.Categories.Displayed.Constructions.FullSubcategory as FS

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Section
open Functorᴰ
-- Terminal category over a base category
Unitᴰ : (C : Category ℓC ℓC') → Categoryᴰ C ℓ-zero ℓ-zero
Unitᴰ C = FullSubcategoryᴰ C (λ _ → Unit)

module _ {C : Category ℓC ℓC'} where
  hasContrHomsUnitᴰ : hasContrHoms (Unitᴰ C)
  hasContrHomsUnitᴰ = hasContrHomsFullSubcategory C _

  ttS : GlobalSection (Unitᴰ C)
  ttS .F-obᴰ  = λ _ → tt
  ttS .F-homᴰ = λ _ → tt
  ttS .F-idᴰ  = refl
  ttS .F-seqᴰ _ _ = refl

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         {F : Functor C D}
         where
  recᴰ : (s : Section F Dᴰ) → Functorᴰ F (Unitᴰ C) Dᴰ
  recᴰ s .F-obᴰ {x} _      = s .F-obᴰ x
  recᴰ s .F-homᴰ {f = f} _ = s .F-homᴰ f
  recᴰ s .F-idᴰ      = s .F-idᴰ
  recᴰ s .F-seqᴰ _ _ = s .F-seqᴰ _ _

-- Terminal category over the terminal category
UnitCᴰ : Categoryᴰ (TerminalCategory {ℓ-zero}) ℓ-zero ℓ-zero
UnitCᴰ = Unitᴰ TerminalCategory
