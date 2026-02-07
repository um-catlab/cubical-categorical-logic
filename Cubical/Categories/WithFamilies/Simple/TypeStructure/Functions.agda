module Cubical.Categories.WithFamilies.Simple.TypeStructure.Functions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.TypeStructure.Base

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  open SCwF S
  FunSpec : (A B : Ty) → TypeSpec S ℓT'
  FunSpec A B = ((Tm A) , comprehension A) ⇒PshSmall Tm B
  
  FunType : (A B : Ty) → Type _
  FunType A B = TyStrUE S $ FunSpec A B

  FunTypes : Type _
  FunTypes = ∀ A B → FunType A B
