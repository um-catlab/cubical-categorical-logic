module Cubical.Categories.LocallySmall.Displayed.Instances.Functor where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Instances.Functor
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Base
open import Cubical.Categories.LocallySmall.Displayed.Properties
open import Cubical.Categories.LocallySmall.Displayed.SmallFibers
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.Base

open Categoryᴰ

open Σω

-- TODO need to change SmallFibNatTransᴰ and FIBER-FUNCTORᴰ
-- to reference SmallDisplayedFiberCategoryᴰ
module _
  {C : SmallCategory ℓC ℓC'}
  {ℓCᴰ ℓCᴰ'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  {D : Category Dob DHom-ℓ}
  {Dob-ℓᴰ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dob-ℓᴰ Dobᴰ DHom-ℓᴰ)
  {E : Category Eob EHom-ℓ}
  {Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ}
  (Dᴰᴰ : SmallFibersᴰCategoryᴰ Dᴰ E Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ)
  where
  private
    module C = CategoryNotation ⟨ C ⟩smallcat
    module Cᴰ = CategoryᴰNotation ⟨ Cᴰ ⟩smallcatᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Dᴰᴰ = SmallFibersᴰCategoryᴰNotation Dᴰᴰ

    C⇒Dᴰ = FIBER-FUNCTOR C Dᴰ
    module C⇒Dᴰ = CategoryᴰNotation C⇒Dᴰ
    ∫C⇒Dᴰ = ∫C (FIBER-FUNCTOR C Dᴰ)
    module ∫C⇒Dᴰ = CategoryNotation ∫C⇒Dᴰ

  open SmallFibNatTrans
  open SmallFibNatTransᴰDefs Cᴰ Dᴰ Dᴰᴰ
  open SmallFibNatTransᴰ

  private
    weaken∫C⇒Dᴰ : Categoryᴰ _ _ _
    weaken∫C⇒Dᴰ = weaken ∫C⇒Dᴰ E
    module weaken∫C⇒Dᴰ = Categoryᴰ weaken∫C⇒Dᴰ

  FIBER-FUNCTORᴰ :
    Categoryᴰ weaken∫C⇒Dᴰ.∫C
      (λ x → Functorᴰ (x .fst .snd) ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ x .fst .fst ][ x .snd ] ⟩smallcatᴰ)
      _
  FIBER-FUNCTORᴰ .Hom[_][_,_] ((f , α) , h) Fᴰ Gᴰ = SmallFibNatTransᴰ h α Fᴰ Gᴰ
  FIBER-FUNCTORᴰ .idᴰ = idSFTransᴰ _
  FIBER-FUNCTORᴰ ._⋆ᴰ_ αᴰ βᴰ = seqSFTransᴰ αᴰ βᴰ
  FIBER-FUNCTORᴰ .⋆IdLᴰ αᴰ =
    makeSFNatTransᴰPath (weaken∫C⇒Dᴰ.⋆IdLᴰ _) (λ xᴰ → Dᴰᴰ.⋆IdLᴰ (αᴰ .N-obᴰ xᴰ))
  FIBER-FUNCTORᴰ .⋆IdRᴰ {x = x}{y = y} αᴰ =
    makeSFNatTransᴰPath (weaken∫C⇒Dᴰ.⋆IdRᴰ _) (λ xᴰ → Dᴰᴰ.⋆IdRᴰ (αᴰ .N-obᴰ xᴰ))
  FIBER-FUNCTORᴰ .⋆Assocᴰ αᴰ βᴰ γᴰ =
    makeSFNatTransᴰPath (weaken∫C⇒Dᴰ.⋆Assocᴰ _ _ _)
      (λ xᴰ → Dᴰᴰ.⋆Assocᴰ (αᴰ .N-obᴰ xᴰ) (βᴰ .N-obᴰ xᴰ) (γᴰ .N-obᴰ xᴰ))
  FIBER-FUNCTORᴰ .isSetHomᴰ = isSetSFNatTransᴰ _ _ _ _
