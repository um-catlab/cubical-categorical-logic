{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.PropertyOver.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Constructions.PropertyOver

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP : Level

open Category
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         (P : ∀ {c} → Categoryᴰ.ob[_] Cᴰ c → Type ℓP) where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ

    PO = (PropertyOver (∫C Cᴰ) (λ { (c , cᴰ) → P cᴰ }))
  open Category
  open Functor
  open Categoryᴰ

  PropertyOverᴰ : Categoryᴰ C (ℓ-max ℓCᴰ ℓP) (ℓ-max ℓCᴰ' ℓ-zero)
  PropertyOverᴰ = ∫Cᴰ Cᴰ PO

  hasPropHomsPropertyOverᴰ : hasPropHoms Cᴰ → hasPropHoms PropertyOverᴰ
  hasPropHomsPropertyOverᴰ hPHCᴰ =
    hasPropHoms∫Cᴰ {C = C}{Cᴰ = Cᴰ} PO hPHCᴰ
      (hasContrHoms→hasPropHoms PO
        (hasContrHomsPropertyOver (∫C {C = C} Cᴰ) λ { (c , cᴰ) → P cᴰ }))
