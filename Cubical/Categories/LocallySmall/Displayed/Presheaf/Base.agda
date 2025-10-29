module Cubical.Categories.LocallySmall.Displayed.Presheaf.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Set
open import Cubical.Categories.LocallySmall.Presheaf.Base
open import Cubical.Categories.LocallySmall.Instances.Functor
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Functor

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.Instances.Set
open import Cubical.Categories.LocallySmall.Displayed.Instances.Functor
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total

open Category
open Categoryᴰ
open Σω
open Liftω

module _
  {C : SmallCategory ℓC ℓC'}
  where
  private
    module SET = CategoryᴰNotation SET

    -- TODO this isn't the best interface
    -- change upon clean up
    module SETᴰ = SmallDisplayedFiberCategoryᴰ SET SETᴰ'''

  module _ {ℓP : Level}  (P : Presheaf C ℓP) where
    module _ (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ') where
      private
        module Cᴰ = CategoryᴰNotation ⟨ Cᴰ ⟩smallcatᴰ

      -- Presheafᴰ : (ℓPᴰ : Level) → Typeω
      -- Presheafᴰ ℓPᴰ =
      --   -- TODO I would like for these displayed functors
      --   -- to be over P, not this composition
      --   Functorᴰ (SET→weakenLevelSET _ _ ∘F P) (⟨ Cᴰ ⟩smallcatᴰ ^opᴰ)
      --     (SETᴰ.vᴰ[ (liftω ℓP) , (liftω ℓPᴰ) ]SF)

      Presheafᴰ' : (ℓPᴰ : Level) → Typeω
      Presheafᴰ' ℓPᴰ =
        -- I'm trying to use ⟨_⟩smallcatᴰ and _^opsmallᴰ
        -- to be helpful, but it may be more trouble than its worth
        -- because they don't necessarily commute
        -- And so I don't know what ought to be the preferred ordering

        Functorᴰ P ⟨ Cᴰ ^opsmallᴰ ⟩smallcatᴰ
          ⟨ SETᴰ.vᴰ[ liftω ℓP ][ ℓPᴰ ] ⟩smallcatᴰ
          -- Nice! no ugly compositions or reindexing

      -- PRESHEAFᴰ : Categoryᴰ (LEVEL ×C LEVEL) _ _
      -- PRESHEAFᴰ =
      --   -- TODO I would like to have FIBER-FUNCTOR into SETᴰ
      --   ∫Cᴰ (FIBER-FUNCTOR (C ^opsmall) weakenLevelSET)
      --       (FIBER-FUNCTORᴰ (Cᴰ ^opsmallᴰ) weakenLevelSET SETᴰ'')

      PRESHEAFᴰ' : Categoryᴰ {!!} _ _
      PRESHEAFᴰ' =
        ∫Cᴰ (FIBER-FUNCTOR (C ^opsmall) SET)
            (FIBER-FUNCTORᴰ (Cᴰ ^opsmallᴰ) {!!} {!!})


      -- module _ {ℓPᴰ} (Pᴰ : Presheafᴰ ℓPᴰ) where
      --   private
      --     module PSHᴰ = CategoryᴰNotation PRESHEAFᴰ
      --     module Pᴰ = FunctorᴰNotation Pᴰ

      --   ∫P : Presheaf (∫Csmall Cᴰ) (ℓ-max ℓP ℓPᴰ)
      --   ∫P = ΣF ∘F (Pᴰ.∫F ∘F help)
      --     where
      --     help :
      --       Functor
      --         (⟨ ∫Csmall Cᴰ ⟩smallcat ^op)
      --         (CategoryᴰNotation.∫C (⟨ Cᴰ ⟩smallcatᴰ ^opᴰ))
      --     help = record {
      --         F-ob = λ z → liftω (z .lowerω .fst) , liftω (z .lowerω .snd)
      --       ; F-hom = λ {x} {y} z → z
      --       ; F-id = refl
      --       ; F-seq = λ _ _ → refl }
