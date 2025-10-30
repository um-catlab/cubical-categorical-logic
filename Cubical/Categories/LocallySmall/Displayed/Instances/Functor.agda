module Cubical.Categories.LocallySmall.Displayed.Instances.Functor where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Instances.Functor
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed
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
  {Dᴰᴰ-ℓ}
  {Dobᴰᴰ : Type Dᴰᴰ-ℓ}
  {Dᴰᴰᴰ-ℓ Dobᴰᴰᴰ DHom-ℓᴰᴰᴰ }
  (Dᴰᴰ : SmallFibersᴰCategoryᴰ Dᴰ Dobᴰᴰ Dᴰᴰᴰ-ℓ Dobᴰᴰᴰ DHom-ℓᴰᴰᴰ)
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
    weaken∫C⇒Dᴰ = weaken ∫C⇒Dᴰ (Indiscrete (Liftω Dobᴰᴰ))
    module weaken∫C⇒Dᴰ = Categoryᴰ weaken∫C⇒Dᴰ


  FIBER-FUNCTORᴰ :
    Categoryᴰ weaken∫C⇒Dᴰ.∫C
      (λ x → Functorᴰ (x .fst .snd) ⟨ Cᴰ ⟩smallcatᴰ ⟨ Dᴰᴰ.vᴰ[ x .fst .fst ][ x .snd .Liftω.lowerω ] ⟩smallcatᴰ)
      _
  FIBER-FUNCTORᴰ .Hom[_][_,_] ((f , α) , _) Fᴰ Gᴰ =
    SmallFibNatTransᴰ α Fᴰ Gᴰ
  FIBER-FUNCTORᴰ .idᴰ = idSFTransᴰ _
  FIBER-FUNCTORᴰ ._⋆ᴰ_ αᴰ βᴰ = seqSFTransᴰ αᴰ βᴰ
  FIBER-FUNCTORᴰ .⋆IdLᴰ {x = x}{y = y} αᴰ =
    makeSFNatTransᴰPath (weaken∫C⇒Dᴰ.⋆IdLᴰ {xᴰ = x .snd} {yᴰ = x .snd} _)
      λ xᴰ → Dᴰᴰ.⋆IdLᴰ (αᴰ .N-obᴰ xᴰ)
  FIBER-FUNCTORᴰ .⋆IdRᴰ {x = x}{y = y} αᴰ =
    makeSFNatTransᴰPath (weaken∫C⇒Dᴰ.⋆IdRᴰ {xᴰ = x .snd} {yᴰ = y .snd} _)
      λ xᴰ → Dᴰᴰ.⋆IdRᴰ (αᴰ .N-obᴰ xᴰ)
  FIBER-FUNCTORᴰ .⋆Assocᴰ {x = x} {y = y} {z = z} {w = w} αᴰ βᴰ γᴰ =
    makeSFNatTransᴰPath
      (weaken∫C⇒Dᴰ.⋆Assocᴰ {xᴰ = x .snd} {yᴰ = y .snd} {zᴰ = z .snd} {wᴰ = w .snd} _ _ _)
      λ xᴰ → Dᴰᴰ.⋆Assocᴰ (αᴰ .N-obᴰ xᴰ) (βᴰ .N-obᴰ xᴰ) (γᴰ .N-obᴰ xᴰ)
  FIBER-FUNCTORᴰ .isSetHomᴰ = isSetSFNatTransᴰ _ _ _
