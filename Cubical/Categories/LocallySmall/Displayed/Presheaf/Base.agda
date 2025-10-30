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
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
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
    module SETᴰ = SmallFibersᴰCategoryᴰNotation SETᴰ

  module _ {ℓP : Level}  (P : Presheaf C ℓP) where
    module _ (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ') where
      private
        module Cᴰ = CategoryᴰNotation ⟨ Cᴰ ⟩smallcatᴰ

      Presheafᴰ : (ℓPᴰ : Level) → Typeω
      Presheafᴰ ℓPᴰ =
        Functorᴰ P ⟨ Cᴰ ^opsmallᴰ ⟩smallcatᴰ
          ⟨ SETᴰ.vᴰ[ liftω ℓP ][ ℓPᴰ ] ⟩smallcatᴰ

      PRESHEAFᴰ : Categoryᴰ (∫C (weaken (∫C (PRESHEAF C)) LEVEL)) _ _
      PRESHEAFᴰ = FIBER-FUNCTORᴰ (Cᴰ ^opsmallᴰ) SET SETᴰ

      -- The locally small displayed category of
      -- globally small displayed presheaves
      -- displayed over the locally small category
      -- of globally small presheaves on a small
      -- category
      -- I love it when word salad is edible
      ∫PRESHEAFᴰ : Categoryᴰ (∫C (PRESHEAF C)) _ _
      ∫PRESHEAFᴰ = ∫Cᴰ _ PRESHEAFᴰ

      -- module _ {ℓPᴰ} (Pᴰ : Presheafᴰ ℓPᴰ) where
      --   private
      --     module PSHᴰ = CategoryᴰNotation PRESHEAFᴰ
      --     module Pᴰ = FunctorᴰNotation Pᴰ

      --   ∫P : Presheaf (∫Csmall Cᴰ) (ℓ-max ℓP ℓPᴰ)
      --   ∫P = {!!} ∘F {!Pᴰ.∫F!}
      -- --   ∫P = ΣF ∘F (Pᴰ.∫F ∘F help)
      -- --     where
      -- --     help :
      -- --       Functor
      -- --         (⟨ ∫Csmall Cᴰ ⟩smallcat ^op)
      -- --         (CategoryᴰNotation.∫C (⟨ Cᴰ ⟩smallcatᴰ ^opᴰ))
      -- --     help = record {
      -- --         F-ob = λ z → liftω (z .lowerω .fst) , liftω (z .lowerω .snd)
      -- --       ; F-hom = λ {x} {y} z → z
      -- --       ; F-id = refl
      -- --       ; F-seq = λ _ _ → refl }
