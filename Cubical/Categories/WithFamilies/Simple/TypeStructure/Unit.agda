module Cubical.Categories.WithFamilies.Simple.TypeStructure.Unit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.WithFamilies.Simple.Base

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

module _ ((C , Ty , Tm , term , ext) : SCwF ℓC ℓC' ℓT ℓT') where
  UnitType : Type _
  UnitType = Σ[ 1Ty ∈ Ty ] PshIso (Tm 1Ty) UnitPsh
