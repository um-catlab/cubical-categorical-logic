{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.More
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

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
    module PSH = Category PSH

  PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP)
    (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓP) (ℓ-suc ℓPᴰ))
    (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓP) ℓPᴰ)
  PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
  PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰ
  PRESHEAFᴰ .idᴰ = idPshHomᴰ
  PRESHEAFᴰ ._⋆ᴰ_ = _⋆PshHomᴰ_
  PRESHEAFᴰ .⋆IdLᴰ {f = α} {yᴰ = Qᴰ} αᴰ = makePshHomᴰPathP _ _ _ opq
    where
    module Qᴰ = PresheafᴰNotation Cᴰ _ Qᴰ
    opaque
      unfolding unfoldPresheafᴰDefs
      opq : makePshHomᴰPathP-Ty (idPshHomᴰ ⋆PshHomᴰ αᴰ) αᴰ (PSH.⋆IdL α)
      opq = funExt₂ λ _ _ → Qᴰ.rectify {e = refl} refl
  PRESHEAFᴰ .⋆IdRᴰ {f = α} {yᴰ = Qᴰ} αᴰ = makePshHomᴰPathP _ _ _ opq
    where
    module Qᴰ = PresheafᴰNotation Cᴰ _ Qᴰ
    opaque
      unfolding unfoldPresheafᴰDefs
      opq : makePshHomᴰPathP-Ty (αᴰ ⋆PshHomᴰ idPshHomᴰ) αᴰ (PSH.⋆IdR α)
      opq = funExt₂ λ _ _ → Qᴰ.rectify {e = refl} refl
  PRESHEAFᴰ .⋆Assocᴰ {wᴰ = Rᴰ} αᴰ βᴰ γᴰ = makePshHomᴰPathP _ _ _ opq
    where
    module Rᴰ = PresheafᴰNotation Cᴰ _ Rᴰ
    opaque
      unfolding unfoldPresheafᴰDefs
      opq : makePshHomᴰPathP-Ty ((αᴰ ⋆PshHomᴰ βᴰ) ⋆PshHomᴰ γᴰ)
                                (αᴰ ⋆PshHomᴰ (βᴰ ⋆PshHomᴰ γᴰ))
                                (PSH.⋆Assoc _ _ _)
      opq = funExt₂ λ _ _ → Rᴰ.rectify {e = refl} refl
  PRESHEAFᴰ .isSetHomᴰ = isSetPshHom _ _
