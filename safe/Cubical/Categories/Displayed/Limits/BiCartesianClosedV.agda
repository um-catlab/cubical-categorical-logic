{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.BiCartesianClosedV where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

record BiCartesianClosedCategoryⱽ
  (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  open CartesianCategory CC
  field
    CCCⱽ : CartesianClosedCategoryⱽ CC ℓCᴰ ℓCᴰ'
  open CartesianClosedCategoryⱽ CCCⱽ public
  field
    initⱽ : Initialsⱽ Cᴰ
    bcpⱽ  : BinCoProductsⱽ Cᴰ
    opcartesianLifts : isFibration (Cᴰ ^opᴰ)

record BiCartesianClosedCategoryᴰ
  (BCCC : BiCartesianClosedCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓC) (ℓ-suc ℓC')) (ℓ-suc ℓCᴰ)) (ℓ-suc ℓCᴰ'))
  where
  open BiCartesianClosedCategory BCCC
  field
    CCCᴰ : CartesianClosedCategoryᴰ CCC ℓCᴰ ℓCᴰ'

  open CartesianClosedCategoryᴰ CCCᴰ public
  field
    initᴰ : Initialᴰ Cᴰ init
    bcpᴰ  : BinCoProductsᴰ Cᴰ sums

  open BinCoProductsᴰNotation Cᴰ sums bcpᴰ public

module _ (BCCC : BiCartesianClosedCategory ℓC ℓC')
  (BCCCⱽ : BiCartesianClosedCategoryⱽ
    (BCCC .BiCartesianClosedCategory.CCC .CartesianClosedCategory.CC)
    ℓCᴰ ℓCᴰ') where
  open BiCartesianClosedCategoryⱽ BCCCⱽ
  open BiCartesianClosedCategory BCCC
  private
    -- Build the "op" CartesianCategory: (C ^op, init, sums)
    CC^op : CartesianCategory _ _
    CC^op .CartesianCategory.C = C ^op
    CC^op .CartesianCategory.term = init
    CC^op .CartesianCategory.bp = sums

    -- Build the "op" vertical cartesian structure from the BiCCC vertical data
    CCⱽ^op : CartesianCategoryⱽ (C ^op) ℓCᴰ ℓCᴰ'
    CCⱽ^op .CartesianCategoryⱽ.Cᴰ = Cᴰ ^opᴰ
    CCⱽ^op .CartesianCategoryⱽ.termⱽ = initⱽ
    CCⱽ^op .CartesianCategoryⱽ.bpⱽ = bcpⱽ
    CCⱽ^op .CartesianCategoryⱽ.cartesianLifts = opcartesianLifts

    -- Apply the existing ⱽ→ᴰ conversion on the op side
    CCᴰ^op : CartesianCategoryᴰ CC^op ℓCᴰ ℓCᴰ'
    CCᴰ^op = CartesianCategoryⱽ→CartesianCategoryᴰ CC^op CCⱽ^op

  open BiCartesianClosedCategoryᴰ

  BiCartesianClosedCategoryⱽ→BiCartesianClosedCategoryᴰ :
    BiCartesianClosedCategoryᴰ BCCC ℓCᴰ ℓCᴰ'
  BiCartesianClosedCategoryⱽ→BiCartesianClosedCategoryᴰ .CCCᴰ =
    CartesianClosedCategoryⱽ→CartesianClosedCategoryᴰ CCC CCCⱽ
  BiCartesianClosedCategoryⱽ→BiCartesianClosedCategoryᴰ .initᴰ =
    CCᴰ^op .CartesianCategoryᴰ.termᴰ
  BiCartesianClosedCategoryⱽ→BiCartesianClosedCategoryᴰ .bcpᴰ =
    CCᴰ^op .CartesianCategoryᴰ.bpᴰ
