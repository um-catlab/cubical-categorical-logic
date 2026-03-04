{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.IntoFiberCategory.Eq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More



open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
import Cubical.Categories.LocallySmall.Functor.Base as LocallySmallF
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.SmallDisplayedFibers
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
import Cubical.Categories.LocallySmall.Displayed.Functor.Base as LocallySmallFᴰ
open import Cubical.Categories.LocallySmall.Displayed.Instances.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Instances.Reindex.Properties
open import Cubical.Categories.LocallySmall.Displayed.Instances.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.IntoFiberCategory.Base

open Category
open Categoryᴰ

open LocallySmallF.Functor
open LocallySmallFᴰ.Functorᴰ
open Liftω
open Σω

module FunctorEqᴰDefs
  {C : SmallCategory ℓC ℓC'}
  {ℓCᴰ ℓCᴰ'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ DHom-ℓᴰ}
  (Dᴰ : GloballySmallCategoryᴰ D Dobᴰ DHom-ℓᴰ)
  {Eob-ℓᴰ Eobᴰ EHom-ℓᴰ}
  (Eᴰ : SmallFibersCategoryᴰ D Eob-ℓᴰ Eobᴰ EHom-ℓᴰ)
  {Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ}
  (Dᴰᴰ : SmallFibersᴰCategoryᴰ Dᴰ Eᴰ Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ)
  where
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰNotation Eᴰ
    module Dᴰᴰ = SmallFibersᴰNotation Dᴰᴰ

  open FunctorᴰDefs Cᴰ Dᴰ Eᴰ Dᴰᴰ

  module _
    (D-⋆ : ∀ {x} → D.id D.⋆ D.id Eq.≡ D.id {x = x})
    (F-seq' : ∀ {d dᴰ} →
     {x y z : Liftω (Eobᴰ d)} (f : Hom[ fibEq Eᴰ D-⋆ d , x ] y)
      (g : Hom[ fibEq Eᴰ D-⋆ d , y ] z) →
      (Categoryᴰ.∫C (Dᴰ ×ᴰ Eᴰ) ⋆
       LocallySmallF.Functor.F-hom (fibᴰEqF D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆) f)
      (LocallySmallF.Functor.F-hom (fibᴰEqF D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆) g)
      Eq.≡
      LocallySmallF.Functor.F-hom (fibᴰEqF D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆)
      ((fibEq Eᴰ D-⋆ d ⋆ f) g))
    where

    FunctorEqᴰ : {d : Dob} → (F : FunctorEq D-⋆ d) → (dᴰ : Dobᴰ d) → Typeω
    FunctorEqᴰ {d} F dᴰ =
      LocallySmallFᴰ.Functorᴰ F
        Cᴰ.catᴰ
        (fibᴰEq D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆ F-seq')

    Functorᴰ→FunctorEqᴰ :
      {d : Dob} → {F : Functor d} → {dᴰ : Dobᴰ d} →
      Functorᴰ F dᴰ →
      FunctorEqᴰ (Functor→FunctorEq D-⋆ d F) dᴰ
    Functorᴰ→FunctorEqᴰ Fᴰ .F-obᴰ = F-obᴰ Fᴰ
    Functorᴰ→FunctorEqᴰ Fᴰ .F-homᴰ = F-homᴰ Fᴰ
    Functorᴰ→FunctorEqᴰ Fᴰ .F-idᴰ =
      F-idᴰ Fᴰ
      ∙ ΣPathP (fib→fibEq Eᴰ D-⋆ _ .F-id ,
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $ sym $ Dᴰᴰ.reind-filler _ _))
    Functorᴰ→FunctorEqᴰ Fᴰ .F-seqᴰ _ _ =
      F-seqᴰ Fᴰ _ _
      ∙ ΣPathP (fib→fibEq Eᴰ D-⋆ _ .F-seq _ _ ,
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $
          (sym $ Dᴰᴰ.reind-filler _ _)
          ∙ Dᴰᴰ.reindEq-pathFiller _ _))

    FunctorEqᴰ→Functorᴰ :
      {d : Dob} → {F : FunctorEq D-⋆ d} → {dᴰ : Dobᴰ d} →
      FunctorEqᴰ F dᴰ →
      Functorᴰ (FunctorEq→Functor D-⋆ d F) dᴰ
    FunctorEqᴰ→Functorᴰ Fᴰ .F-obᴰ = F-obᴰ Fᴰ
    FunctorEqᴰ→Functorᴰ Fᴰ .F-homᴰ = F-homᴰ Fᴰ
    FunctorEqᴰ→Functorᴰ Fᴰ .F-idᴰ =
      F-idᴰ Fᴰ
      ∙ ΣPathP (fibEq→fib Eᴰ D-⋆ _ .F-id ,
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $ Dᴰᴰ.reind-filler _ _))
    FunctorEqᴰ→Functorᴰ Fᴰ .F-seqᴰ _ _ =
      F-seqᴰ Fᴰ _ _
      ∙ ΣPathP (fibEq→fib Eᴰ D-⋆ _ .F-seq _ _ ,
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $
          (sym $ Dᴰᴰ.reindEq-pathFiller _ _)
          ∙ Dᴰᴰ.reind-filler _ _))
