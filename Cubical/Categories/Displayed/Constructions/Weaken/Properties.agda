{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Weaken.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ
open UniversalElementᴰ
open UniversalElement
open isIsoOver
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  module _ (termC : Terminal' C) (termD : Terminal' D) where
    termWeaken : Terminalᴰ (weaken C D) termC
    termWeaken .vertexᴰ = termD .vertex
    termWeaken .elementᴰ = termD .element
    termWeaken .universalᴰ {xᴰ = d} .inv _ _ =
      UniversalElementNotation.intro termD _
    termWeaken .universalᴰ {xᴰ = d} .rightInv _ _ = refl
    termWeaken .universalᴰ {xᴰ = d} .leftInv f g =
      sym $ UniversalElementNotation.η termD
  module _ (prodC : BinProducts C)(prodD : BinProducts D) where
    private module B = BinProductsNotation prodD
    binprodWeaken : BinProductsᴰ (weaken C D) prodC
    binprodWeaken _ .vertexᴰ = prodD _ .vertex
    binprodWeaken _ .elementᴰ = prodD _ .element
    binprodWeaken _ .universalᴰ .inv _ (g₁ , g₂) = g₁ B.,p g₂
    binprodWeaken _ .universalᴰ .rightInv _ (g₁ , g₂) =
      UniversalElementNotation.β (prodD _)
    binprodWeaken _ .universalᴰ .leftInv _ g = sym $ B.×ue.η _ _

module _ (C : CartesianCategory ℓC ℓC') (D : CartesianCategory ℓD ℓD') where
  open CartesianCategory renaming (C to Cat)
  open CartesianCategoryᴰ
  weakenCartesianCategory : CartesianCategoryᴰ C ℓD ℓD'
  weakenCartesianCategory .Cᴰ = weaken (C .Cat) (D .Cat)
  weakenCartesianCategory .termᴰ = termWeaken (C .term) (D .term)
  weakenCartesianCategory .bpᴰ = binprodWeaken (C .bp) (D .bp)
