module Cubical.Categories.Instances.TotalCategory.More where


open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Instances.TotalCategory

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  open Functor
  open Functorᴰ
  open Section

  ∫C-op-commute : Functor (∫C Cᴰ ^op) (∫C (Cᴰ ^opᴰ))
  ∫C-op-commute = intro (Fst ^opF) (Snd ^opS)
