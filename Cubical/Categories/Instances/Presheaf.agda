module Cubical.Categories.Instances.Presheaf where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
  variable ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

open Category
-- TODO: move these upstream
PRESHEAF : (C : Category ℓC ℓC') (ℓP : Level) → Category _ _
PRESHEAF C ℓP .ob = Presheaf C ℓP
PRESHEAF C ℓP .Hom[_,_] = PshHom
PRESHEAF C ℓP .id = idPshHom
PRESHEAF C ℓP ._⋆_ = _⋆PshHom_
PRESHEAF C ℓP .⋆IdL = λ f → makePshHomPath refl
PRESHEAF C ℓP .⋆IdR = λ f → makePshHomPath refl
PRESHEAF C ℓP .⋆Assoc = ⋆PshHomAssoc
PRESHEAF C ℓP .isSetHom = isSetPshHom _ _
