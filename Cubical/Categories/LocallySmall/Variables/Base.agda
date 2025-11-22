module Cubical.Categories.LocallySmall.Variables.Base where

open import Cubical.Foundations.Prelude

variable
  ℓ ℓ' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓP ℓQ ℓR : Level
  ℓᴰ ℓᴰ' ℓ1ᴰ ℓ2ᴰ ℓwᴰ ℓxᴰ ℓyᴰ ℓzᴰ : Level
  ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level
  ℓPᴰ ℓQᴰ ℓRᴰ : Level

  Cob Dob Eob : Typeω
  CHom-ℓ DHom-ℓ EHom-ℓ : Cob → Cob → Level
  Cobᴰ : Cob → Typeω
  Dobᴰ : Dob → Typeω
  Eobᴰ : Eob → Typeω
  CHom-ℓᴰ DHom-ℓᴰ EHom-ℓᴰ : ∀ (x y : Cob)(xᴰ : Cobᴰ x)(yᴰ : Cobᴰ y) → Level
