module Cubical.Categories.WithFamilies.Simple.TypeStructure.Functions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.LevelsSyntax

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
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓT ℓT' ℓTᴰ ℓTᴰ' ℓD ℓD' ℓS ℓS' : Level

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  open SCwFNotation S

  FunType : (A B : ⟨ Ty ⟩) → Type _
  FunType A B =
    Σ[ A⇒B ∈ ⟨ Ty ⟩ ]
    PshIso (Tm A⇒B) ((Tm A , ext A) ⇒PshSmall Tm B)

  FunTypes : Type _
  FunTypes = ∀ A B → FunType A B

  record hasFunctionTypes : Type ⌈ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ 0ℓ ⌉ℓ where
    field function-types : FunTypes

  open hasFunctionTypes {{...}} public

  module _ (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') where
    open SCwFᴰNotation S Sᴰ hiding (Ty)

    module _
      {A B : ⟨ Ty ⟩}
      ((A⇒B , A⇒B≅) : FunType A B)
      (Aᴰ : ⟨ Tyᴰ A ⟩) (Bᴰ : ⟨ Tyᴰ B ⟩)
      where
      FunTypeᴰ : Type _
      FunTypeᴰ =
        Σ[ Aᴰ⇒Bᴰ ∈ ⟨ Tyᴰ A⇒B ⟩ ]
          PshIsoᴰ A⇒B≅ (Tmᴰ Aᴰ⇒Bᴰ) ((Tmᴰ Aᴰ , extᴰ Aᴰ) ⇒PshSmallᴰ Tmᴰ Bᴰ)

      module _ (Fᴰ : SCwFSection S Sᴰ) where
        open Section

        preservesFunType : Type _
        preservesFunType =
          preservesUE (Fᴰ .fst) (Fᴰ .snd .snd .fst A⇒B)
            (TmUE S A⇒B)

    module _ (funs : FunTypes) where
      FunTypesᴰ : Type _
      FunTypesᴰ =
        ∀ {A B : ⟨ Ty ⟩} →
        (Aᴰ : ⟨ Tyᴰ A ⟩) (Bᴰ : ⟨ Tyᴰ B ⟩) →
        FunTypeᴰ (funs A B) Aᴰ Bᴰ

      record hasFunctionTypesᴰ :
        Type ⌈ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ ℓCᴰ ,ℓ ℓCᴰ' ,ℓ ℓTᴰ ,ℓ ℓTᴰ' ,ℓ 0ℓ ⌉ℓ where
        field function-typesᴰ : FunTypesᴰ

      open hasFunctionTypesᴰ {{...}} public
