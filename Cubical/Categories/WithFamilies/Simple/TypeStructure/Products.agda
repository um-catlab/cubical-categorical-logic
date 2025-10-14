module Cubical.Categories.WithFamilies.Simple.TypeStructure.Products where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Section.Base

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Properties
open import Cubical.Categories.WithFamilies.Simple.Displayed

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  open SCwFNotation S
  ProdType : (A B : Ty) → Type _
  ProdType A B =
    Σ[ A×B ∈ Ty ] PshIso (Tm A×B) (Tm A ×Psh Tm B)

  ProdTypes : Type _
  ProdTypes = ∀ A B → ProdType A B

  module _ (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓS ℓS') where
    open SCwFᴰNotation Sᴰ hiding (Ty)
    module _ {A B : Ty}
      ((A×B , A×B≅) : ProdType A B)
      (Aᴰ : Tyᴰ A) (Bᴰ : Tyᴰ B)
      where
      ProdTypeᴰ : Type _
      ProdTypeᴰ =
        Σ[ Aᴰ×Bᴰ ∈ Tyᴰ A×B ]
          PshIsoᴰ A×B≅ (Tmᴰ Aᴰ×Bᴰ) (Tmᴰ Aᴰ ×ᴰPsh Tmᴰ Bᴰ)

      module _ (Fᴰ : SCwFSection S Sᴰ) where
        open Section

        preservesProdType : Type _
        preservesProdType =
          preservesUE (Fᴰ .fst) (Fᴰ .snd .snd .fst A×B)
            (TmUE S A×B)
