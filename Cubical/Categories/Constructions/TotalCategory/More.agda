module Cubical.Categories.Constructions.TotalCategory.More where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Constructions.TotalCategory
-- open import Cubical.Categories.Displayed.Instances.Terminal.Base
-- import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  open Functor
  open Functorᴰ
  open Section

  ∫C-op-commute : Functor (∫C Cᴰ ^op) (∫C (Cᴰ ^opᴰ))
  ∫C-op-commute = intro (Fst ^opF) (Snd ^opS)
