module Cubical.Categories.WithFamilies.Simple.TypeStructure.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Presheaf.Constructions.Unit
open import Cubical.Categories.Displayed.Section.Base

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Properties
open import Cubical.Categories.WithFamilies.Simple.Displayed

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  open SCwFNotation S

  UnitType : Type _
  UnitType = Σ[ 1Ty ∈ Ty ] PshIso (Tm 1Ty) UnitPsh

  module _
    ((1Ty , 1Ty≅) : UnitType)
    (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓS ℓS') where
    open SCwFᴰNotation Sᴰ
    UnitTypeᴰ : Type _
    UnitTypeᴰ =
      Σ[ 1Tyᴰ ∈ Tyᴰ 1Ty ]
        PshIsoᴰ 1Ty≅ (Tmᴰ 1Tyᴰ) UnitPshᴰ

    module _ (Fᴰ : SCwFSection S Sᴰ) where
      open Section

      preservesUnitType : Type _
      preservesUnitType =
        preservesUE (Fᴰ .fst) (Fᴰ .snd .snd .fst 1Ty)
          (TmUE S 1Ty)
