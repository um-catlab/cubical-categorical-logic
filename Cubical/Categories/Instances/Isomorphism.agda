module Cubical.Categories.Instances.Isomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Constructions.ChangeOfObjects

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.HomPropertyOver

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  private
    module C = Category C

  open HomPropertyOver
  ISOProperty : HomPropertyOver C ℓ'
  ISOProperty .Hom[_][-,-] = isIso C
  ISOProperty .isPropHomᴰ f = isPropIsIso f
  ISOProperty .idᴰ = idCatIso .snd
  ISOProperty ._⋆ᴰ_ f g isIso-f isIso-g = compIso (g , isIso-g) (f , isIso-f) .snd

  ISO : Category _ _
  ISO = HomPropertyOver→Cat ISOProperty
