module Cubical.Categories.WithFamilies.Simple.TypeStructure.Products where

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
  ProdType : (A B : Ty) → Type _
  ProdType A B =
    Σ[ A×B ∈ Ty ] PshIso (Tm A×B) (Tm A ×Psh Tm B)

  ProdTypes : Type _
  ProdTypes = ∀ A B → ProdType A B
