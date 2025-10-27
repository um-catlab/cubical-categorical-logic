module Cubical.Categories.LocallySmall.Displayed.Instances.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Prod using (_×ω_; _,_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Base as LocallySmall
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Instances.Functor
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.Base

open Category
open Categoryᴰ

open Functorᴰ
open SmallFibNatTrans
open Liftω
open Σω
module _
  {(Cob , C) : SmallCategory ℓC ℓC'}
  {ℓCᴰ ℓCᴰ'}
  ((Cobᴰ , Cᴰ) : SmallCategoryᴰ ((Cob , C)) ℓCᴰ ℓCᴰ')
  {D : Category Dob DHom-ℓ}
  {Dob-ℓᴰ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dob-ℓᴰ Dobᴰ DHom-ℓᴰ)
  {Eob-ℓᴰ Eobᴰ}
  {EHom-ℓᴰ : Dob → Dob → Level}
  (Eᴰ : SmallFibersCategoryᴰ (∫C Dᴰ) Eob-ℓᴰ Eobᴰ λ u v → EHom-ℓᴰ (u .fst ) (v .fst))
  where
  private
    module C = CategoryNotation C
    module Cᴰ = CategoryᴰNotation Cᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰOver∫SFNotation Eᴰ

  open SmallFibNatTrans
  open SmallFibNatTransᴰDefs (Cobᴰ , Cᴰ) Dᴰ Eᴰ
  open SmallFibNatTransᴰ

  FIBER-FUNCTORᴰ :
    Categoryᴰ (∫C (FIBER-FUNCTOR (Cob , C) Dᴰ))
      (λ (d , F) → Functorᴰ F Cᴰ Eᴰ.vᴰ[ d ]SF)
      {!!}
  FIBER-FUNCTORᴰ .Hom[_][_,_] (f , α) Fᴰ Gᴰ =
    SmallFibNatTransᴰ α Fᴰ Gᴰ
  FIBER-FUNCTORᴰ .idᴰ = idSFTransᴰ _
  FIBER-FUNCTORᴰ ._⋆ᴰ_ αᴰ βᴰ = seqSFTransᴰ αᴰ βᴰ
  FIBER-FUNCTORᴰ .⋆IdLᴰ = {!!}
  FIBER-FUNCTORᴰ .⋆IdRᴰ = {!!}
  FIBER-FUNCTORᴰ .⋆Assocᴰ = {!!}
  FIBER-FUNCTORᴰ .isSetHomᴰ = {!!}
