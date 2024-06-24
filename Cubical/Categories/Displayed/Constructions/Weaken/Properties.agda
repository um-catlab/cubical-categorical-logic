{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Weaken.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Constructions.TotalCategory as TC
  hiding (intro)
open import Cubical.Categories.Constructions.TotalCategory.More as TC
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ
open UniversalElementᴰ
open UniversalElement
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  module _ (termC : Terminal' C) (termD : Terminal' D) where
    termWeaken : LiftedTerminal (weaken C D) termC
    termWeaken .vertexᴰ = termD .vertex
    termWeaken .elementᴰ = termD .element
    termWeaken .universalᴰ = termD .universal _
  module _ (prodC : BinProducts' C)(prodD : BinProducts' D) where
    private module B = BinProducts'Notation prodD
    binprodWeaken : LiftedBinProducts (weaken C D) prodC
    binprodWeaken _ .vertexᴰ = prodD _ .vertex
    binprodWeaken _ .elementᴰ = prodD _ .element
    binprodWeaken _ .universalᴰ = prodD _ .universal _
