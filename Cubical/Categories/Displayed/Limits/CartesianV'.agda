{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.CartesianV' where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

record CartesianCategoryⱽ (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  constructor cartesiancategoryⱽ
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termⱽ : Terminalsⱽ Cᴰ
    bpⱽ   : BinProductsⱽ Cᴰ
    cartesianLifts : isFibration Cᴰ
  module Cᴰ = Categoryᴰ Cᴰ

record CartesianCategoryᴰ (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  constructor cartesiancategoryᴰ
  open CartesianCategory CC
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termᴰ : Terminalᴰ Cᴰ term
    bpᴰ : BinProductsᴰ Cᴰ bp
  module Cᴰ = Fibers Cᴰ
  module termᴰ = UniversalElementᴰNotation Cᴰ _ _ termᴰ
  module bpᴰ = BinProductsᴰNotation Cᴰ bp bpᴰ

module _ (CC : CartesianCategory ℓC ℓC') where
  private
    module CC = CartesianCategory CC
  open CartesianCategoryⱽ
  open CartesianCategoryᴰ
  open UniversalElement
  CartesianCategoryⱽ→CartesianCategoryᴰ : CartesianCategoryⱽ CC.C ℓCᴰ ℓCᴰ' → CartesianCategoryᴰ CC ℓCᴰ ℓCᴰ'
  CartesianCategoryⱽ→CartesianCategoryᴰ CCⱽ .Cᴰ = CCⱽ .Cᴰ
  CartesianCategoryⱽ→CartesianCategoryᴰ CCⱽ .termᴰ = Terminalⱽ→ᴰ (CCⱽ .Cᴰ) CC.term (CCⱽ .termⱽ _)
  CartesianCategoryⱽ→CartesianCategoryᴰ CCⱽ .bpᴰ {A}{B} Aᴰ Bᴰ = BinProductⱽ→ᴰ (CCⱽ .Cᴰ) (CC.bp _) Aᴰ Bᴰ
    (CCⱽ .bpⱽ (CCⱽ .cartesianLifts Aᴰ (CC.bp (A , B) .vertex) (CC.bp (A , B) .element .fst) .fst)
              (CCⱽ .cartesianLifts Bᴰ (CC.bp (A , B) .vertex) (CC.bp (A , B) .element .snd) .fst)
              .fst
    , CCⱽ .bpⱽ _ _ .snd
      ⋆PshIso ×PshIso
        (CCⱽ .cartesianLifts Aᴰ (CC.bp (A , B) .vertex) (CC.bp (A , B) .element .fst) .snd)
        (CCⱽ .cartesianLifts Bᴰ (CC.bp (A , B) .vertex) (CC.bp (A , B) .element .snd) .snd)
      )
