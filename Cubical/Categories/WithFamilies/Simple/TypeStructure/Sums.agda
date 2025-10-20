module Cubical.Categories.WithFamilies.Simple.TypeStructure.Sums where

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
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Properties
open import Cubical.Categories.WithFamilies.Simple.Displayed

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  open SCwFNotation S

  open ContinuationPresheaf (C , Ty , Tm , term , ext)

  SumType : (A B : ⟨ Ty ⟩) → Type _
  SumType A B =
    Σ[ A+B ∈ ⟨ Ty ⟩ ] ∀ (C : ⟨ Ty ⟩) →
      -- ∀ Γ
      -- Γ , A + B ⊢ C iff Γ , A ⊢ C and Γ , B ⊢ C
      PshIso (Cont A+B C) (Cont A C ×Psh Cont B C)

  SumTypes : Type _
  SumTypes = ∀ A B → SumType A B

  record hasSumTypes : Type ⌈ ℓC ,ℓ ℓC' ,ℓ ℓT ,ℓ ℓT' ,ℓ 0ℓ ⌉ℓ where
    field sum-types : SumTypes

  open hasSumTypes {{...}} public

  -- module _ (Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓS ℓS') where
  --   open SCwFᴰNotation Sᴰ hiding (Ty)
  --   module _ {A B : Ty}
  --     ((A+B , A+B≅) : SumType A B)
  --     (Aᴰ : Tyᴰ A) (Bᴰ : Tyᴰ B)
  --     where
  --     -- TODO Contᴰ
  --     SumTypeᴰ : Type _
  --     SumTypeᴰ =
  --       Σ[ Aᴰ+Bᴰ ∈ Tyᴰ A+B ] ?
