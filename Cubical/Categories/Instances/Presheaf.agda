module Cubical.Categories.Instances.Presheaf where

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

-- open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
-- open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
-- open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Limits.Cartesian.Base

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
  variable ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

open Category
-- TODO: move these upstream
module _ (C : Category ℓC ℓC') (ℓP : Level) where
  PRESHEAF : Category _ _
  PRESHEAF .ob = Presheaf C ℓP
  PRESHEAF .Hom[_,_] = PshHom
  PRESHEAF .id = idPshHom
  PRESHEAF ._⋆_ = _⋆PshHom_
  PRESHEAF .⋆IdL = λ f → makePshHomPath refl
  PRESHEAF .⋆IdR = λ f → makePshHomPath refl
  PRESHEAF .⋆Assoc = ⋆PshHomAssoc
  PRESHEAF .isSetHom = isSetPshHom _ _

  open UniversalElementNotation
  Cartesian-PRESHEAF : CartesianCategory _ _
  Cartesian-PRESHEAF .CartesianCategory.C = PRESHEAF
  Cartesian-PRESHEAF .CartesianCategory.term .vertex = Unit*Psh
  Cartesian-PRESHEAF .CartesianCategory.term .element = tt
  Cartesian-PRESHEAF .CartesianCategory.term .universal R =
    isoToIsEquiv
      (iso (λ _ → tt) (λ _ → Unit*Psh-intro) (λ _ → refl) λ _ → makePshHomPath refl)
  Cartesian-PRESHEAF .CartesianCategory.bp (P , Q) .vertex = P ×Psh Q
  Cartesian-PRESHEAF .CartesianCategory.bp (P , Q) .element =
    (π₁ P Q) , (π₂ P Q)
  Cartesian-PRESHEAF .CartesianCategory.bp (P , Q) .universal R =
    isoToIsEquiv (×Psh-UMP P Q)
