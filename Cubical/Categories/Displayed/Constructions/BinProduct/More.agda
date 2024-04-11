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

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
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

-- Product within a fiber
-- TODO: replace this with ∫ᴰ ?

-- TODO: is there an easy way to reduce this code duplication?
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

  open Categoryᴰ
  private
    module Dᴰ₀ = Categoryᴰ Dᴰ₀
    module Dᴰ₁ = Categoryᴰ Dᴰ₁
    module Dᴰ× = Categoryᴰ (Dᴰ₀ ×ᴰ Dᴰ₁)

  open Functorᴰ
  introF : Functorᴰ F Eᴰ (Dᴰ₀ ×ᴰ Dᴰ₁)
  introF .F-obᴰ x = Fᴰ₀ .F-obᴰ x , Fᴰ₁ .F-obᴰ x
  introF .F-homᴰ fᴰ =  Fᴰ₀ .F-homᴰ fᴰ , Fᴰ₁ .F-homᴰ fᴰ
  introF .F-idᴰ = ΣPathP (Fᴰ₀ .F-idᴰ , Fᴰ₁ .F-idᴰ)
  introF .F-seqᴰ fᴰ gᴰ = ΣPathP (Fᴰ₀ .F-seqᴰ fᴰ gᴰ , Fᴰ₁ .F-seqᴰ fᴰ gᴰ)
