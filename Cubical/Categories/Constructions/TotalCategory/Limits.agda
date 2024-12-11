{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.TotalCategory.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning as Reasoning
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf

open import Cubical.Categories.Constructions.TotalCategory.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

-- Total category of a displayed category
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open UniversalElementᴰ
  open isIsoOver
  private
    module CᴰR = Reasoning Cᴰ
  ∫term : (term : Terminal C) → Terminalᴰ Cᴰ (terminalToUniversalElement term)
    → Terminal (∫C Cᴰ)
  ∫term term termᴰ .fst = term .fst , termᴰ .vertexᴰ
  ∫term term termᴰ .snd (x , xᴰ) = uniqueExists
    (term .snd x .fst)
    (termᴰ .universalᴰ .inv _ _)
    (λ f fᴰ fᴰ' →
      CᴰR.rectify $ CᴰR.≡out $
        (CᴰR.≡in $ ηᴰ termᴰ) ∙ (sym $ CᴰR.≡in $ ηᴰ termᴰ))
    λ f fᴰ → term .snd x .snd f
