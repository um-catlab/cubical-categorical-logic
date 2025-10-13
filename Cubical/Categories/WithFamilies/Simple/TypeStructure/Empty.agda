module Cubical.Categories.WithFamilies.Simple.TypeStructure.Empty where

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

  open ContinuationPresheaf (C , Ty , Tm , term , ext)

  EmptyType : Type _
  EmptyType =
    Σ[ 0Ty ∈ Ty ] ∀ (C : Ty) →
      PshIso (Cont 0Ty C) EmptyPsh

  -- PreservesEmptyType :
