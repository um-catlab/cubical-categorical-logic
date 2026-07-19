-- Lists over a carrier, well-ordered by length.
module Cubical.Categories.Direct.Instances.ListByLength where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.List using (length)
open import Cubical.Data.List.Properties using (isOfHLevelList)

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)
open import Cubical.Categories.Direct.Instances.Poset

private
  variable
    ℓ : Level

module _ (A : Type ℓ) (isSetA : isSet A) where
  ListWFOrder : WFOrder ℓ ℓ-zero
  ListWFOrder = pullbackWFOrder ℕWFOrder (isOfHLevelList 0 isSetA) length

  ListCat = PosetCat ListWFOrder

  ListDirect : DirectStr {C = ListCat} ListWFOrder
  ListDirect = PosetDirect ListWFOrder
