module Cubical.Categories.Displayed.Constructions.Reindex.Properties where

open import Cubical.Foundations.Prelude


open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D
    F*Dᴰ = reindex Dᴰ F
    module R = HomᴰReasoning Dᴰ
    module F*Dᴰ = Categoryᴰ F*Dᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  hasPropHomsReindex : hasPropHoms Dᴰ → hasPropHoms (reindex Dᴰ F)
  hasPropHomsReindex = λ z {c} {c'} f → z (F-hom F f)

  π-FFᴰ : FullyFaithfulᴰ (π Dᴰ F)
  π-FFᴰ f xᴰ yᴰ = (λ z → z) , ((λ _ → refl) , (λ _ → refl))

-- module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
--   {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
--   (F : Functor C D) where

--   CartesianLiftReindex : ∀ {c c'}{dᴰ}{f : C [ c , c' ]} →
--     CartesianLift Dᴰ dᴰ (F ⟪ f ⟫) →
--     CartesianLift (reindex Dᴰ F) dᴰ f
--   CartesianLiftReindex cL =
--     reindUEⱽ cL ◁PshIsoⱽ
--       (invPshIsoⱽ (reindYoReindFunc {F = F})
--       ⋆PshIsoⱽ reindPshIsoⱽ (yoRec (C [-, _ ]) _) reindⱽFuncRepr)

--   isFibrationReindex
--     : isFibration Dᴰ
--     → isFibration (reindex Dᴰ F)
--   isFibrationReindex isFib xᴰ f =
--     CartesianLiftReindex $ isFib xᴰ (F ⟪ f ⟫)
