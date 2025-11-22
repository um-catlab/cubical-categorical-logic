module Cubical.Categories.LocallySmall.Instances.Functor.ResizeFibered where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
import Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibered as SmallFibNat
import Cubical.Categories.LocallySmall.NaturalTransformation.Fibered as FibNat
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered.Base
open import Cubical.Categories.LocallySmall.Instances.Functor.SmallFibered.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base


open Category
open Categoryᴰ
open Liftω

module _
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (C : SmallCategory ℓC ℓC')
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C =  SmallCategory C
    module D =  CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ

  open Functorᴰ
  FIBERED-FUNCTOR→SMALL-FIBERED-FUNCTOR :
    Functorⱽ (FIBERED-FUNCTOR C Dᴰ) (SMALL-FIBERED-FUNCTOR C Dᴰ)
  FIBERED-FUNCTOR→SMALL-FIBERED-FUNCTOR .F-obᴰ F =
    liftω (SmallLocallySmallFunctor→SmallFunctor F)
  FIBERED-FUNCTOR→SMALL-FIBERED-FUNCTOR .F-homᴰ =
    λ α → SmallFibNat.natTrans
      (α .FibNat.FibNatTrans.N-ob) (α .FibNat.FibNatTrans.N-hom)
  FIBERED-FUNCTOR→SMALL-FIBERED-FUNCTOR .F-idᴰ =
    SmallFibNat.makeSFNatTransPath refl λ _ → refl
  FIBERED-FUNCTOR→SMALL-FIBERED-FUNCTOR .F-seqᴰ _ _ =
    SmallFibNat.makeSFNatTransPath refl λ _ → refl

  SMALL-FIBERED-FUNCTOR→FIBERED-FUNCTOR :
    Functorⱽ (SMALL-FIBERED-FUNCTOR C Dᴰ) (FIBERED-FUNCTOR C Dᴰ)
  SMALL-FIBERED-FUNCTOR→FIBERED-FUNCTOR .F-obᴰ (liftω F) =
    mkSmallCategoryF-elim ∘F mkSmallFunctor F ∘F mkSmallCategoryF-intro
  SMALL-FIBERED-FUNCTOR→FIBERED-FUNCTOR .F-homᴰ α =
    FibNat.natTrans
      (α .SmallFibNat.SmallFibNatTrans.N-ob)
      (α .SmallFibNat.SmallFibNatTrans.N-hom)
  SMALL-FIBERED-FUNCTOR→FIBERED-FUNCTOR .F-idᴰ =
    FibNat.makeFibNatTransPath refl λ _ → refl
  SMALL-FIBERED-FUNCTOR→FIBERED-FUNCTOR .F-seqᴰ _ _ =
    FibNat.makeFibNatTransPath refl λ _ → refl
