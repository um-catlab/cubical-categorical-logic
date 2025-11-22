module Cubical.Categories.LocallySmall.Displayed.Functor.Constant where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Functor
open Functorᴰ
module _
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  {d : Dob}
  (dᴰ : Dobᴰ d)
  where
  private
    module Dᴰ = Categoryᴰ Dᴰ
  Constantᴰ : Functorᴰ (Constant d) Cᴰ Dᴰ
  Constantᴰ .F-obᴰ = λ z → dᴰ
  Constantᴰ .F-homᴰ = λ fᴰ → Categoryᴰ.idᴰ Dᴰ
  Constantᴰ .F-idᴰ = refl
  Constantᴰ .F-seqᴰ = λ _ _ → sym (Dᴰ.⋆IdLᴰ _)
