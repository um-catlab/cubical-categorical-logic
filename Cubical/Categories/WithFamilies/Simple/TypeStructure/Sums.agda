module Cubical.Categories.WithFamilies.Simple.TypeStructure.Sums where

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

  SumType : (A B : Ty) → Type _
  SumType A B =
    Σ[ A+B ∈ Ty ] ∀ (C : Ty) →
      PshIso (Cont A+B C) (Cont A C ×Psh Cont B C)

  SumTypes : Type _
  SumTypes = ∀ A B → SumType A B
