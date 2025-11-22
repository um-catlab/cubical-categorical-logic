{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Displayed.Instances.Functor.SmallFibered where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Instances.Unit
open import Cubical.Categories.LocallySmall.Instances.Functor.SmallFibered.Base
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibered
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.SmallFibered.Base

open Category
open Categoryᴰ

open Functorᴰ
open SmallFibNatTrans
open Liftω
open Σω

module SmallFiberedFunctorCategoryᴰ
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
    module Dᴰᴰ = CategoryᴰNotation Dᴰᴰ

    C⇒Eᴰ : SmallFibersCategoryᴰ D _ (SmallFiberedFunctor C Eᴰ) _
    C⇒Eᴰ = SMALL-FIBERED-FUNCTOR C Eᴰ

    Dᴰ×C⇒Eᴰ = Dᴰ ×ᴰ C⇒Eᴰ
    Dᴰ×Eᴰ = Dᴰ ×ᴰ Eᴰ
    module Dᴰ×C⇒Eᴰ = CategoryᴰNotation Dᴰ×C⇒Eᴰ
    module Dᴰ×Eᴰ = CategoryᴰNotation Dᴰ×Eᴰ

  open SmallFibNatTransᴰDefs Cᴰ Dᴰ Eᴰ Dᴰᴰ public
  open SmallFibNatTransᴰ

  SMALL-FIBERED-FUNCTORᴰ :
    SmallFibersᴰCategoryᴰ
      Dᴰ C⇒Eᴰ _ (λ (d , dᴰ , F) → SmallFiberedFunctorᴰ (F .lowerω) dᴰ) _
  SMALL-FIBERED-FUNCTORᴰ .Hom[_][_,_] (f , fᴰ , α) xᴰ yᴰ =
    SmallFibNatTransᴰ fᴰ α (xᴰ .lowerω) (yᴰ .lowerω)
  SMALL-FIBERED-FUNCTORᴰ .idᴰ = idSFTransᴰ _
  SMALL-FIBERED-FUNCTORᴰ ._⋆ᴰ_ = seqSFTransᴰ
  SMALL-FIBERED-FUNCTORᴰ .⋆IdLᴰ αᴰ =
    makeSFNatTransᴰPath (Dᴰ×C⇒Eᴰ.⋆IdLᴰ _)
      (λ xᴰ → Dᴰᴰ.⋆IdLᴰ (αᴰ .N-obᴰ xᴰ))
  SMALL-FIBERED-FUNCTORᴰ .⋆IdRᴰ  αᴰ =
    makeSFNatTransᴰPath (Dᴰ×C⇒Eᴰ.⋆IdRᴰ _)
      (λ xᴰ → Dᴰᴰ.⋆IdRᴰ (αᴰ .N-obᴰ xᴰ))
  SMALL-FIBERED-FUNCTORᴰ .⋆Assocᴰ αᴰ βᴰ γᴰ =
    makeSFNatTransᴰPath (Dᴰ×C⇒Eᴰ.⋆Assocᴰ _ _ _)
      (λ xᴰ → Dᴰᴰ.⋆Assocᴰ (αᴰ .N-obᴰ xᴰ) (βᴰ .N-obᴰ xᴰ) (γᴰ .N-obᴰ xᴰ))
  SMALL-FIBERED-FUNCTORᴰ .isSetHomᴰ = isSetSFNatTransᴰ _ _ _ _
