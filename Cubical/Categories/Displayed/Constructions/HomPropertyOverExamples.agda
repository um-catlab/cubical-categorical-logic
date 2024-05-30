module Cubical.Categories.Displayed.Constructions.HomPropertyOverExamples where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Displayed.Base

open import Cubical.Categories.Displayed.Constructions.HomPropertyOver

private
  variable
    ℓC ℓC' : Level

module _ (C : Category ℓC ℓC') where
  open Category C

  private
    isIsoC = isIso C

    idIsIsoC : ∀ {x} → isIsoC (id {x})
    idIsIsoC = idCatIso .snd

    compP : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]} → isIsoC f → isIsoC g → isIsoC (f ⋆ g)
    compP {f = f} {g = g} fIso gIso = ⋆Iso (f , fIso) (g , gIso) .snd

  -- Given as an example of a wide subcategory on nlab:
  -- https://ncatlab.org/nlab/show/core+groupoid
  Core : Categoryᴰ C ℓ-zero ℓC'
  Core = HomPropertyOver C isIsoC (isPropIsIso _) idIsIsoC compP
