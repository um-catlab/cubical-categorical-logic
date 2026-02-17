{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.CartesianD where

open import Cubical.Data.Sigma

open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Lift
open import Cubical.Categories.Displayed.Presheaf.Constructions.Unit
open import Cubical.Categories.Displayed.Presheaf.Representable

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

record CartesianCategoryᴰ (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  open CartesianCategory CC
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termᴰ : Terminalᴰ Cᴰ term
    bpᴰ   : BinProductsᴰ Cᴰ bp

  module Cᴰ = Categoryᴰ Cᴰ

record CartesianCategoryReprᴰ (CC : CartesianCategoryRepr ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  open CartesianCategoryRepr CC
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ' -- (TerminalPresheafᴰ* Cᴰ ℓCᴰ' (TerminalPresheaf* ℓC'))
    termᴰ : Representationᵁᴰ Cᴰ (LiftPshᴰ UnitPshᴰ ℓCᴰ') term
    bpᴰ   : ∀ {c} {d} cᴰ dᴰ
      → Representationᵁᴰ Cᴰ ((Cᴰ [-][-, cᴰ ]) ×ᴰPsh (Cᴰ [-][-, dᴰ ])) (bp c d)

  module Cᴰ = Categoryᴰ Cᴰ
