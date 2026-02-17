{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Functions.FunExtEquiv


open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base

open Category
open Functor
open PshHom
open PshIso
open Categoryᴰ

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' : Level

module _
  (C : Category ℓC ℓC')
  (ℓP ℓPᴰ : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  private
    PSH = PRESHEAF C ℓP
  PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
  PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰ
  PRESHEAFᴰ .idᴰ = idPshHomᴰ
  PRESHEAFᴰ ._⋆ᴰ_ = _⋆PshHomᴰ_
  PRESHEAFᴰ .⋆IdLᴰ {f = α} {yᴰ = Qᴰ} αᴰ =
    makePshHomᴰPathP _ _ _ (funExt₂ λ _ _ → Qᴰ.rectify {e = refl} refl)
    where
    module Qᴰ = PresheafᴰNotation Cᴰ _ Qᴰ
  PRESHEAFᴰ .⋆IdRᴰ {yᴰ = Qᴰ} _ =
    makePshHomᴰPathP _ _ _ (funExt₂ λ _ _ → Qᴰ.rectify {e = refl} refl)
    where
    module Qᴰ = PresheafᴰNotation Cᴰ _ Qᴰ
  PRESHEAFᴰ .⋆Assocᴰ {wᴰ = Rᴰ} _ _ _ =
    makePshHomᴰPathP _ _ _ (funExt₂ λ _ _ → Rᴰ.rectify {e = refl} refl)
    where
    module Rᴰ = PresheafᴰNotation Cᴰ _ Rᴰ
  PRESHEAFᴰ .isSetHomᴰ = isSetPshHom _ _
