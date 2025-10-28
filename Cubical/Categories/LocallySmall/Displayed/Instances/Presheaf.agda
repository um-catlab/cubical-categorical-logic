module Cubical.Categories.LocallySmall.Displayed.Instances.Presheaf where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Set
open import Cubical.Categories.LocallySmall.Instances.Presheaf
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
  {(Cob , C) : SmallCategory ℓC ℓC'}
  where
  private
    module SET = CategoryᴰNotation SET
    module SETᴰ = ∫CᴰSETᴰNotation

  module _ {ℓP : Level}  (P : Presheaf (Cob , C) ℓP) where
    module _ ((Cobᴰ , Cᴰ) : SmallCategoryᴰ (Cob , C) ℓCᴰ ℓCᴰ') where
      Presheafᴰ : (ℓPᴰ : Level) → Typeω
      Presheafᴰ ℓPᴰ =
        -- TODO I would like for these displayed functors
        -- to be over P, not this composition
        Functorᴰ (SET→weakenLevelSET _ _ ∘F P) (Cᴰ ^opᴰ)
          (SETᴰ.vᴰ[ (liftω ℓP) , (liftω ℓPᴰ) ]SF)

      PRESHEAFᴰ : Categoryᴰ (LEVEL ×C LEVEL) _ _
      PRESHEAFᴰ =
        -- TODO I would like to have FIBER-FUNCTOR into SETᴰ
        ∫Cᴰ (FIBER-FUNCTOR (Cob , C ^op) weakenLevelSET)
            (FIBER-FUNCTORᴰ (Cobᴰ , Cᴰ ^opᴰ) weakenLevelSET SETᴰ'')
