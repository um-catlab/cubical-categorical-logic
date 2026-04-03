-- TODO:
--                          Dᴰ
-- a section Fᴰ over F : C → D
--
-- can be weakened to be a functorᴰ for any Cᴰ
module Cubical.Categories.Displayed.Section.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Equality
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base


private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Categoryᴰ
open Functor

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F : Functor C D}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         (Fᴰ : Section F Dᴰ)
         where
  wkSection : Functorᴰ F Cᴰ Dᴰ
  wkSection .Functorᴰ.F-obᴰ = λ z → Fᴰ .Section.F-obᴰ _
  wkSection .Functorᴰ.F-homᴰ = λ z → Fᴰ .Section.F-homᴰ _
  wkSection .Functorᴰ.F-idᴰ = Fᴰ .Section.F-idᴰ
  wkSection .Functorᴰ.F-seqᴰ = λ fᴰ gᴰ → Fᴰ .Section.F-seqᴰ _ _
