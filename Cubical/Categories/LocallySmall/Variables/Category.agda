module Cubical.Categories.LocallySmall.Variables.Category where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.LocallySmall.Variables.Base public
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small

module CategoryVariables where
  variable
    C : Category Cob CHom-ℓ
    D : Category Dob DHom-ℓ
    E : Category Eob EHom-ℓ

module CategoryᴰVariables where
  open CategoryVariables public
  variable
    Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ
    Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ
    Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ

module SmallCategoryVariables where
  variable
    C : SmallCategory ℓC ℓC'
    D : SmallCategory ℓD ℓD'
    E : SmallCategory ℓD ℓD'

module SmallCategoryᴰVariables where
  open SmallCategoryVariables public
  variable
    Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ'
    Dᴰ : SmallCategoryᴰ D ℓDᴰ ℓDᴰ'
    Eᴰ : SmallCategoryᴰ E ℓEᴰ ℓEᴰ'
