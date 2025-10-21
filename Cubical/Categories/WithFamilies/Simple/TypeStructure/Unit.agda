module Cubical.Categories.WithFamilies.Simple.TypeStructure.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.LevelsSyntax
open import Cubical.Foundations.More

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
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓT ℓT' ℓTᴰ ℓTᴰ' ℓD ℓD' ℓS ℓS' : Level

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  open SCwFNotation S

  UnitType : Type _
  UnitType = Σ[ 1Ty ∈ Ty ] PshIso (Tm 1Ty) UnitPsh

  record hasUnitType : Type ⌈ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ 0ℓ ⌉ℓ where
    field
      unit-type : UnitType
    -- TODO naming
    -- the-unit-type : Ty
    -- the-unit-type = unit-type .fst

    -- the-unit-type-iso : PshIso (Tm the-unit-type) UnitPsh
    -- the-unit-type-iso = unit-type .snd

  open hasUnitType {{...}} public

  module _ (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') where
    open SCwFᴰNotation S Sᴰ
    module _ ((1Ty , 1Ty≅) : UnitType) where
      UnitTypeᴰ : Type _
      UnitTypeᴰ =
        Σ[ 1Tyᴰ ∈ Tyᴰ 1Ty ]
          PshIsoᴰ 1Ty≅ (Tmᴰ 1Tyᴰ) UnitPshᴰ

      record hasUnitTypeᴰ :
        Type ⌈ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ ℓCᴰ ,ℓ ℓCᴰ' ,ℓ ℓTᴰ ,ℓ ℓTᴰ' ,ℓ 0ℓ ⌉ℓ where
        field unit-typeᴰ : UnitTypeᴰ

      open hasUnitTypeᴰ {{...}} public

      module _ (Fᴰ : SCwFSection S Sᴰ) where
        open Section

        preservesUnitType : Type _
        preservesUnitType =
          preservesUE (Fᴰ .fst) (Fᴰ .snd .snd .fst 1Ty)
            (TmUE S 1Ty)
