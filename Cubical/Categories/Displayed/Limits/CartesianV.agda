{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.CartesianV where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Properties
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.CartesianD
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

record CartesianCategoryⱽ (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termⱽ : Terminalsⱽ Cᴰ
    bpⱽ   : BinProductsⱽ Cᴰ
  module Cᴰ = Categoryᴰ Cᴰ
  field
    cartesianLifts : isFibration Cᴰ

module _ {CC : CartesianCategory ℓC ℓC'}
         (CCᴰ : CartesianCategoryⱽ (CC .CartesianCategory.C) ℓCᴰ ℓCᴰ') where
  open CartesianCategory CC
  open CartesianCategoryⱽ CCᴰ
  open CartesianCategoryᴰ hiding (Cᴰ)
  private
    module bp = BinProductsNotation bp
  CartesianCategoryⱽ→CartesianCategoryᴰ : CartesianCategoryᴰ CC ℓCᴰ ℓCᴰ'
  CartesianCategoryⱽ→CartesianCategoryᴰ .CartesianCategoryᴰ.Cᴰ = Cᴰ
  CartesianCategoryⱽ→CartesianCategoryᴰ .termᴰ = termⱽ 𝟙ue.vertex ◁PshIsoⱽᴰ UnitPshᴰ≅UnitPshᴰ
  CartesianCategoryⱽ→CartesianCategoryᴰ .bpᴰ =
    BinProductsⱽ→BinProductsᴰ Cᴰ cartesianLifts bpⱽ bp

record CartesianCategoryReprⱽ (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
  module Cᴰ = Categoryᴰ Cᴰ
  field
    termⱽ : ∀ {c} → Representationᵁⱽ Cᴰ {c = c} (LiftPshᴰ UnitPshᴰ ℓCᴰ')
    bpⱽ   : ∀ {c} (cᴰ dᴰ : Cᴰ.ob[ c ])
      → Representationᵁⱽ Cᴰ ((Cᴰ [-][-, cᴰ ]) ×ⱽPsh (Cᴰ [-][-, dᴰ ]))
    cartesianLifts : ∀ {c d} (f : C [ c , d ]) (dᴰ : Cᴰ.ob[ d ])
      → Representationᵁⱽ Cᴰ (reindYo f (Cᴰ [-][-, dᴰ ]))

module _ {CC : CartesianCategoryRepr ℓC ℓC'}
         (CCᴰ : CartesianCategoryReprⱽ (CC .CartesianCategoryRepr.C) ℓCᴰ ℓCᴰ') where
  open CartesianCategoryRepr CC
  open CartesianCategoryReprⱽ CCᴰ
  open CartesianCategoryReprᴰ hiding (Cᴰ)
  CartesianCategoryⱽ→CartesianCategoryReprᴰ : CartesianCategoryReprᴰ CC ℓCᴰ ℓCᴰ'
  CartesianCategoryⱽ→CartesianCategoryReprᴰ .CartesianCategoryReprᴰ.Cᴰ = Cᴰ
  CartesianCategoryⱽ→CartesianCategoryReprᴰ .termᴰ = _ ,
    termⱽ .snd
    ◁ Lift-Path UnitPshᴰ≡UnitPshᴰ
  CartesianCategoryⱽ→CartesianCategoryReprᴰ .bpᴰ cᴰ dᴰ =
    _ , ( bpⱽ _ _ .snd
        ◁ ×ᴰ≡π₁*×ⱽπ₂* (bp _ _) (cartesianLifts _ cᴰ) (cartesianLifts _ dᴰ))
