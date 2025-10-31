module Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Base
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken.Base
open import Cubical.Categories.LocallySmall.Variables

open Category
open Categoryᴰ
open Σω

module _ (C : Category Cob CHom-ℓ)(D : Category Dob DHom-ℓ) where
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
  open Functor
  ∫weakenSwap : Functor (∫C (weaken C D)) (∫C (weaken D C))
  ∫weakenSwap .F-ob = λ z → z .snd , z .fst
  ∫weakenSwap .F-hom = λ z → z .snd , z .fst
  ∫weakenSwap .F-id = refl
  ∫weakenSwap .F-seq = λ _ _ → refl
