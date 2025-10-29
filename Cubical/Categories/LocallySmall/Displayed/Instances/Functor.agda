module Cubical.Categories.LocallySmall.Displayed.Instances.Functor where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Instances.Functor
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.Base

open Categoryᴰ

open Σω

-- TODO need to change SmallFibNatTransᴰ and FIBER-FUNCTORᴰ
-- to reference SmallDisplayedFiberCategoryᴰ
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

    C⇒Dᴰ = FIBER-FUNCTOR (Cob , C) Dᴰ
    module C⇒Dᴰ = CategoryᴰNotation C⇒Dᴰ
    ∫C⇒Dᴰ = ∫C (FIBER-FUNCTOR (Cob , C) Dᴰ)
    module ∫C⇒Dᴰ = CategoryNotation ∫C⇒Dᴰ

  open SmallFibNatTrans
  open SmallFibNatTransᴰDefs (Cobᴰ , Cᴰ) Dᴰ Eᴰ
  open SmallFibNatTransᴰ

  FIBER-FUNCTORᴰ :
    Categoryᴰ ∫C⇒Dᴰ
      (λ (d , F) → Functorᴰ F Cᴰ Eᴰ.vᴰ[ d ]SF)
      _
  FIBER-FUNCTORᴰ .Hom[_][_,_] (f , α) Fᴰ Gᴰ =
    SmallFibNatTransᴰ α Fᴰ Gᴰ
  FIBER-FUNCTORᴰ .idᴰ = idSFTransᴰ _
  FIBER-FUNCTORᴰ ._⋆ᴰ_ αᴰ βᴰ = seqSFTransᴰ αᴰ βᴰ
  FIBER-FUNCTORᴰ .⋆IdLᴰ αᴰ =
    makeSFNatTransᴰPath (C⇒Dᴰ.⋆IdLᴰ _)
      λ xᴰ → Eᴰ.⋆IdLᴰ (αᴰ .N-obᴰ xᴰ)
  FIBER-FUNCTORᴰ .⋆IdRᴰ αᴰ =
    makeSFNatTransᴰPath (C⇒Dᴰ.⋆IdRᴰ _)
      λ xᴰ → Eᴰ.⋆IdRᴰ (αᴰ .N-obᴰ xᴰ)
  FIBER-FUNCTORᴰ .⋆Assocᴰ αᴰ βᴰ γᴰ =
    makeSFNatTransᴰPath (C⇒Dᴰ.⋆Assocᴰ _ _ _)
      λ xᴰ → Eᴰ.⋆Assocᴰ (αᴰ .N-obᴰ xᴰ) (βᴰ .N-obᴰ xᴰ) (γᴰ .N-obᴰ xᴰ)
  FIBER-FUNCTORᴰ .isSetHomᴰ = isSetSFNatTransᴰ _ _ _
