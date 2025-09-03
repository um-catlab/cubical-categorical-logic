{- A section of a displayed presheaf -}
module Cubical.Categories.Displayed.Presheaf.Section where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Terminal as Terminal
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Section

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open PshHomᴰ
open Section

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} (F : GlobalSection Cᴰ) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  PshSection : Type _
  PshSection =
    PshHomⱽ {Cᴰ = Unitᴰ C} (UnitPshᴰ {P = P}) (Pᴰ ∘Fᴰⱽ (Terminal.recᴰ F ^opFⱽ))

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  (F : GlobalSection Cᴰ)(α : PshSection F Pᴰ)
  (ue : UniversalElement C P)
  where
  open UniversalElement
  open UniversalElementᴰ
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Cᴰ = Categoryᴰ Cᴰ
    elementOverUE = (Σ[ v ∈ Cᴰ.ob[ ue .vertex ] ] Pᴰ.p[ ue .element ][ v ])
  -- Strict preservation is when vertex ↦ vertexᴰ and element ↦ elementᴰ
  strictlyPreservesUE : (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ) → Type _
  strictlyPreservesUE ueᴰ =
    Path elementOverUE
      ((F .F-obᴰ (ue .vertex)) , (α .N-obᴰ _))
      ((ueᴰ .vertexᴰ) , (ueᴰ .elementᴰ))

  -- weak preservation doesn't require the a priori existence of ueᴰ
  preservesUE : Type _
  preservesUE =
    isUniversalᴰ Cᴰ ue Pᴰ (F .F-obᴰ (ue .vertex)) (α .N-obᴰ {p = ue .element} _)

  strictlyPreservesUE→preservesUE :
    (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ)
    → strictlyPreservesUE ueᴰ → preservesUE
  strictlyPreservesUE→preservesUE ueᴰ ue↦ueᴰ =
    subst isUniversalᴰ' (sym ue↦ueᴰ) (ueᴰ .universalᴰ)
    where
      isUniversalᴰ' : elementOverUE → Type _
      isUniversalᴰ' (vᴰ , eᴰ) = isUniversalᴰ Cᴰ ue Pᴰ vᴰ eᴰ
