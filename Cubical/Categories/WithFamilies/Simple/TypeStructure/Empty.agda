module Cubical.Categories.WithFamilies.Simple.TypeStructure.Empty where

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
open import Cubical.Categories.Displayed.Presheaf.Constructions.Empty

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Properties
open import Cubical.Categories.WithFamilies.Simple.Displayed

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  open SCwFNotation S

  EmptyType : Type ⌈ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ 0ℓ ⌉ℓ
  EmptyType =
    Σ[ 0Ty ∈ Ty ] ∀ (C : Ty) →
      PshIso (Cont 0Ty C) EmptyPsh

  record hasEmptyType : Type ⌈ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ 0ℓ ⌉ℓ where
    field
      empty-type : EmptyType

  open hasEmptyType {{...}} public

  -- module _
  --   ((0Ty , 0Ty≅) : EmptyType)
  --   (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓS ℓS') where
  --   open SCwFᴰNotation Sᴰ hiding (Ty)

  --   -- TODO Contᴰ
  --   EmptyTypeᴰ : Type _
  --   EmptyTypeᴰ =
  --     Σ[ 0Tyᴰ ∈ Tyᴰ 0Ty ]
  --       ∀ {A} (Aᴰ : Tyᴰ A) → PshIsoᴰ (0Ty≅ A) {!!} EmptyPshᴰ
