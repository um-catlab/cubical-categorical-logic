{-# OPTIONS --lossy-unification #-}
module Gluing.BiCartesianClosedCategory.BinaryLogicalRelation where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.BinProduct.Cartesian
  renaming (_×_ to _×CC_)
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedV
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Quiver
open import Cubical.Categories.Instances.Free.BiCartesianClosedCategory.Forded
  as FreeBiCCC

private
  variable
    ℓC ℓC' ℓD ℓD' ℓQ ℓQ' ℓDⱽ ℓDⱽ' : Level

module _
  (Q : +×⇒Quiver ℓQ ℓQ')
  (D : BiCartesianClosedCategory ℓD ℓD')
  (Dⱽ : BiCartesianClosedCategoryⱽ
    (D .BiCartesianClosedCategory.CC)
    ℓDⱽ ℓDⱽ')
  where

  private
    FREE : BiCartesianClosedCategory _ _
    FREE = FreeBiCartesianClosedCategory Q

    module FREE = BiCartesianClosedCategory FREE
    module D = BiCartesianClosedCategory D
    module Dⱽ = BiCartesianClosedCategoryⱽ Dⱽ

  module _
    (product : CartesianFunctor (D.CC ×CC D.CC) D.C)
    (F G : CartesianFunctor FREE.CC D.C)
    where

    paired : CartesianFunctor FREE.CC (D.C ×C D.C)
    paired = pairCF {B = FREE.CC} {C = D.CC} {D = D.CC} F G

    pointwise : CartesianFunctor FREE.CC D.C
    pointwise =
      _∘CF_ {C = FREE.CC} {D = D.CC ×CC D.CC}
        product paired

    -- Data for a relation on generating objects together with proofs
    -- that every generating arrow preserves it.
    LogicalRelationGenerators : Type _
    LogicalRelationGenerators =
      FreeBiCCC.ElimInterpᴰ Q
        (FreeBiCCC.elimLocalMotive Q pointwise Dⱽ)

    -- The fundamental lemma: generator data extends to all freely
    -- generated bicartesian-closed objects and arrows.
    logicalRelation :
      LogicalRelationGenerators →
      Section (pointwise .fst) Dⱽ.Cᴰ
    logicalRelation =
      FreeBiCCC.elimLocal Q pointwise Dⱽ
