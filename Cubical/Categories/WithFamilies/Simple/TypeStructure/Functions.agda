module Cubical.Categories.WithFamilies.Simple.TypeStructure.Functions where

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
open import Cubical.Categories.Displayed.Presheaf.Constructions.Exponential
open import Cubical.Categories.Displayed.Section.Base

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Properties
open import Cubical.Categories.WithFamilies.Simple.Displayed

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  open SCwFNotation S

  FunType : (A B : Ty) → Type _
  FunType A B =
    Σ[ A⇒B ∈ Ty ]
    PshIso (Tm A⇒B) ((Tm A , ext A) ⇒PshSmall Tm B)

  FunTypes : Type _
  FunTypes = ∀ A B → FunType A B

  module _ (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓS ℓS') where
    open SCwFᴰNotation Sᴰ hiding (Ty)

    module _
      {A B : Ty}
      ((A⇒B , A⇒B≅) : FunType A B)
      (Aᴰ : Tyᴰ A) (Bᴰ : Tyᴰ B)
      where
      FunTypeᴰ : Type _
      FunTypeᴰ =
        Σ[ Aᴰ⇒Bᴰ ∈ Tyᴰ A⇒B ]
          PshIsoᴰ A⇒B≅ (Tmᴰ Aᴰ⇒Bᴰ) ((Tmᴰ Aᴰ , extᴰ Aᴰ) ⇒PshSmallᴰ Tmᴰ Bᴰ)

      module _ (Fᴰ : SCwFSection S Sᴰ) where
        open Section

        preservesFunType : Type _
        preservesFunType =
          preservesUE (Fᴰ .fst) (Fᴰ .snd .snd .fst A⇒B)
            (TmUE S A⇒B)
