{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.BiCartesianClosedV where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV

import Cubical.Categories.Displayed.Limits.BiCartesianClosedV as Path
import Cubical.Categories.Displayed.Limits.CartesianClosedV as Path
import Cubical.Categories.Displayed.Limits.CartesianV' as Path

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ (CC : CartesianCategory ℓC ℓC') where
  private
    module CC = CartesianCategory CC
  module _
    (⋆AssocC : ReprEqAssoc CC.C)
    (⋆IdLC : EqIdL CC.C)
    (π₁NatEqC : Allπ₁NatEq CC.bp)
    (×aF-seqC : All×aF-seq CC.bp)
    (Cᴰ : Categoryᴰ CC.C ℓCᴰ ℓCᴰ')
    (⋆AssocC^op : ReprEqAssoc (CC.C ^op))
    where
    EqBCCCⱽ→BCCCⱽ :
        isCartesianClosedⱽ {C = CC.C} ⋆AssocC Cᴰ ⋆IdLC CC.bp π₁NatEqC ×aF-seqC
      → isCartesianⱽ {C = CC.C ^op} ⋆AssocC^op (Cᴰ ^opᴰ)
      → Path.BiCartesianClosedCategoryⱽ CC ℓCᴰ ℓCᴰ'
    EqBCCCⱽ→BCCCⱽ isCCCⱽ isCartⱽ^op .Path.BiCartesianClosedCategoryⱽ.CCCⱽ =
      EqCCCⱽ→CCCⱽ CC ⋆AssocC ⋆IdLC π₁NatEqC ×aF-seqC Cᴰ isCCCⱽ
    EqBCCCⱽ→BCCCⱽ isCCCⱽ isCartⱽ^op .Path.BiCartesianClosedCategoryⱽ.initⱽ =
      ccⱽ^op .Path.CartesianCategoryⱽ.termⱽ
      where ccⱽ^op = EqCCⱽ→CCⱽ ⋆AssocC^op (Cᴰ ^opᴰ) isCartⱽ^op
    EqBCCCⱽ→BCCCⱽ isCCCⱽ isCartⱽ^op .Path.BiCartesianClosedCategoryⱽ.bcpⱽ =
      ccⱽ^op .Path.CartesianCategoryⱽ.bpⱽ
      where ccⱽ^op = EqCCⱽ→CCⱽ ⋆AssocC^op (Cᴰ ^opᴰ) isCartⱽ^op
    EqBCCCⱽ→BCCCⱽ isCCCⱽ isCartⱽ^op .Path.BiCartesianClosedCategoryⱽ.opcartesianLifts =
      ccⱽ^op .Path.CartesianCategoryⱽ.cartesianLifts
      where ccⱽ^op = EqCCⱽ→CCⱽ ⋆AssocC^op (Cᴰ ^opᴰ) isCartⱽ^op
