{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.IntoFiberCategory.Eq where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
import Cubical.Categories.Functor as SmallFunctor
import Cubical.Categories.Displayed.Functor as SmallFunctorᴰ

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Instances.Unit
open import Cubical.Categories.LocallySmall.Instances.Functor.IntoFiberCategory
import Cubical.Categories.LocallySmall.Functor.Base as LocallySmallF
open import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.SmallDisplayedFibers
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
import Cubical.Categories.LocallySmall.Displayed.Functor.Base as LocallySmallFᴰ
import Cubical.Categories.LocallySmall.Displayed.Functor.Properties as LocallySmallFᴰ
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base
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
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $ sym $ Dᴰᴰ.reind-filler))
    Functorᴰ→FunctorEqᴰ Fᴰ .F-seqᴰ _ _ =
      F-seqᴰ Fᴰ _ _
      ∙ ΣPathP (fib→fibEq Eᴰ D-⋆ _ .F-seq _ _ ,
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $
          (sym $ Dᴰᴰ.reind-filler)
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
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $ Dᴰᴰ.reind-filler))
    FunctorEqᴰ→Functorᴰ Fᴰ .F-seqᴰ _ _ =
      F-seqᴰ Fᴰ _ _
      ∙ ΣPathP (fibEq→fib Eᴰ D-⋆ _ .F-seq _ _ ,
        (Dᴰᴰ.rectify $ Dᴰᴰ.≡out $
          (sym $ Dᴰᴰ.reindEq-pathFiller _ _)
          ∙ Dᴰᴰ.reind-filler _))
