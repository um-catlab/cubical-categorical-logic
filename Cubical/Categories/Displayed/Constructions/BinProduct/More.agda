{-
    Binary Product of displayed categories over the same base.

    TODO: this can be defined as an instance of TotalCategoryᴰ using
    weakening. Should it?

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.BinProduct.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Constructions.TotalCategory
  as TotalCat
open import Cubical.Categories.Displayed.Constructions.TotalCategory
  as TotalCatᴰ hiding (introS; introF)
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
  hiding (introF)
open import Cubical.Categories.Displayed.Reasoning as Reasoning
private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level
    ℓBᴰ ℓBᴰ' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level
    ℓDᴰ₀ ℓDᴰ₀' ℓDᴰ₁ ℓDᴰ₁' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
  where

  open Functorᴰ
  private
    module D = Categoryᴰ D

  ΔCᴰ : Functorᴰ (Δ C) D (D ×Cᴰ D)
  ΔCᴰ .F-obᴰ xᴰ = xᴰ , xᴰ
  ΔCᴰ .F-homᴰ fᴰ = fᴰ , fᴰ
  ΔCᴰ .F-idᴰ = refl
  ΔCᴰ .F-seqᴰ fᴰ gᴰ = refl

  Δᴰ : Functorᴰ Id D (D ×ᴰ D)
  Δᴰ .F-obᴰ xᴰ = xᴰ , xᴰ
  Δᴰ .F-homᴰ fᴰ = fᴰ , fᴰ
  Δᴰ .F-idᴰ = refl
  Δᴰ .F-seqᴰ fᴰ gᴰ = refl

module _
  {B : Category ℓB ℓB'} {Bᴰ : Categoryᴰ B ℓBᴰ ℓBᴰ'}
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {E : Category ℓE ℓE'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  {F : Functor B C}{G : Functor D E}
  (Fᴰ : Functorᴰ F Bᴰ Cᴰ) (Gᴰ : Functorᴰ G Dᴰ Eᴰ)
  where
  open Functorᴰ
  private
    module RCᴰ = Reasoning Cᴰ
    module REᴰ = Reasoning Eᴰ
  _×Fᴰ_ : Functorᴰ (F ×F G) (Bᴰ ×Cᴰ Dᴰ) (Cᴰ ×Cᴰ Eᴰ)
  _×Fᴰ_ .F-obᴰ x = (F-obᴰ Fᴰ (x .fst)) , (F-obᴰ Gᴰ (x .snd))
  _×Fᴰ_ .F-homᴰ f = F-homᴰ Fᴰ (f .fst) , F-homᴰ Gᴰ (f .snd)
  _×Fᴰ_ .F-idᴰ = ΣPathP (RCᴰ.rectify (F-idᴰ Fᴰ) , REᴰ.rectify (Gᴰ .F-idᴰ))
  _×Fᴰ_ .F-seqᴰ fᴰ gᴰ =
    ΣPathP ((RCᴰ.rectify (Fᴰ .F-seqᴰ _ _)) , REᴰ.rectify (Gᴰ .F-seqᴰ _ _))

module _ {C : Category ℓC ℓC'}
  {Dᴰ₀ : Categoryᴰ C ℓDᴰ₀ ℓDᴰ₀'} {Dᴰ₁ : Categoryᴰ C ℓDᴰ₁ ℓDᴰ₁'}
  {E : Category ℓE ℓE'}
  (F : Functor E C)
  (Fᴰ₀ : Section F Dᴰ₀)
  (Fᴰ₁ : Section F Dᴰ₁)
  where

  open Section
  introS : Section F (Dᴰ₀ ×ᴰ Dᴰ₁)
  introS .F-obᴰ d =  Fᴰ₀ .F-obᴰ d , Fᴰ₁ .F-obᴰ d
  introS .F-homᴰ fᴰ = Fᴰ₀ .F-homᴰ fᴰ , Fᴰ₁ .F-homᴰ fᴰ
  introS .F-idᴰ = ΣPathP (Fᴰ₀ .F-idᴰ , Fᴰ₁ .F-idᴰ)
  introS .F-seqᴰ fᴰ gᴰ = ΣPathP (Fᴰ₀ .F-seqᴰ fᴰ gᴰ , Fᴰ₁ .F-seqᴰ fᴰ gᴰ)

module _ {C : Category ℓC ℓC'}
  {Dᴰ₀ : Categoryᴰ C ℓDᴰ₀ ℓDᴰ₀'} {Dᴰ₁ : Categoryᴰ C ℓDᴰ₁ ℓDᴰ₁'}
  {E : Category ℓE ℓE'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  (F : Functor E C)
  (Fᴰ₀ : Functorᴰ F Eᴰ Dᴰ₀)
  (Fᴰ₁ : Functorᴰ F Eᴰ Dᴰ₁)
  where

  introF : Functorᴰ F Eᴰ (Dᴰ₀ ×ᴰ Dᴰ₁)
  introF = TotalCat.recᴰ F _
    (introS _ (TotalCat.elim Fᴰ₀) (TotalCat.elim Fᴰ₁))

private
  -- In principle we can also define introS in terms of introF in
  -- terms of Functorᴰs as follows:
  module _ {C : Category ℓC ℓC'}
    {Dᴰ₀ : Categoryᴰ C ℓDᴰ₀ ℓDᴰ₀'} {Dᴰ₁ : Categoryᴰ C ℓDᴰ₁ ℓDᴰ₁'}
    {E : Category ℓE ℓE'}
    (F : Functor E C)
    (Fᴰ₀ : Section F Dᴰ₀)
    (Fᴰ₁ : Section F Dᴰ₁)
    where

    open Section
    introS' : Section F (Dᴰ₀ ×ᴰ Dᴰ₁)
    introS' = compFunctorᴰGlobalSection
      (introF F (Unitᴰ.recᴰ Fᴰ₀) (Unitᴰ.recᴰ Fᴰ₁))
      ttS
