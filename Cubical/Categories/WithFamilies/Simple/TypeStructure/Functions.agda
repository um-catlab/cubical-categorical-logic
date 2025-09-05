module Cubical.Categories.WithFamilies.Simple.TypeStructure.Functions where

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
  FunType : (A B : Ty) → Type _
  FunType A B =
    Σ[ A⇒B ∈ Ty ]
    -- TODO check with Max
    -- this was originally written with the Presheaf.Properties version
    -- of PshIso
    -- I changed it to the Presheaf.Morphism.Alt version
    PshIso (Tm A⇒B) (((Tm A) , λ Γ → ext Γ A) ⇒PshSmall Tm B)

  FunTypes : Type _
  FunTypes = ∀ A B → FunType A B
