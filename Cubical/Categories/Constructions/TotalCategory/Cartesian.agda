{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.TotalCategory.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

import Cubical.Categories.Constructions.TotalCategory as TC
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Limits.Cartesian

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _
  {C : CartesianCategory ℓC ℓC'}
  (Cᴰ : CartesianCategoryᴰ C ℓCᴰ ℓCᴰ')
  where
  open UniversalElement
  open BinProduct
  private
    module C = CartesianCategoryNotation C
    module Cᴰ = CartesianCategoryᴰNotation Cᴰ
  ∫C : CartesianCategory (ℓ-max ℓC ℓCᴰ) (ℓ-max ℓC' ℓCᴰ')
  ∫C .fst = TC.∫C (Cᴰ .fst)
  ∫C .snd .fst = (_ , Cᴰ.𝟙ᴰ) , (λ _ → (_ , Cᴰ.!tᴰ _) , λ _ → ΣPathP (C.𝟙η' , Cᴰ.𝟙η'ᴰ _ _))
  ∫C .snd .snd cᴰ c'ᴰ .binProdOb = (cᴰ .fst C.×bp c'ᴰ .fst) , (cᴰ .snd Cᴰ.×ᴰ c'ᴰ .snd)
  ∫C .snd .snd cᴰ c'ᴰ .binProdPr₁ = C.π₁ , Cᴰ.π₁ᴰ
  ∫C .snd .snd cᴰ c'ᴰ .binProdPr₂ = C.π₂ , Cᴰ.π₂ᴰ
  ∫C .snd .snd cᴰ c'ᴰ .univProp f g = uniqueExists
    (_ , (f .snd Cᴰ.,pᴰ g .snd))
    ((ΣPathP (C.×β₁ , Cᴰ.×β₁ᴰ)) , (ΣPathP (C.×β₂ , Cᴰ.×β₂ᴰ)))
    (λ _ → isProp× (isSetΣ C.isSetHom (λ _ → Cᴰ.isSetHomᴰ) _ _) (isSetΣ C.isSetHom (λ _ → Cᴰ.isSetHomᴰ) _ _))
    λ _ p → ΣPathP (C.×η'' (sym (cong fst (p .fst))) (symP (cong fst (p .snd))) , Cᴰ.×η''ᴰ (symP (cong snd (p .fst))) (symP (cong snd (p .snd))))
