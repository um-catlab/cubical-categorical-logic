module Cubical.Categories.Displayed.Instances.ChangeOfObjects where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.ChosenReind

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓX : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  {X : Category.ob C → Type ℓX} (F : ∀ {c} → X c → Categoryᴰ.ob[_] Cᴰ c)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  open Categoryᴰ
  open Functorᴰ

  ChangeOfObjectsᴰ : Categoryᴰ C ℓX ℓCᴰ'
  ChangeOfObjectsᴰ .ob[_] = X
  ChangeOfObjectsᴰ .Hom[_][_,_] f a b = Cᴰ.Hom[ f ][ F a , F b ]
  ChangeOfObjectsᴰ .idᴰ = Cᴰ.idᴰ
  ChangeOfObjectsᴰ ._⋆ᴰ_ = Cᴰ._⋆ᴰ_
  ChangeOfObjectsᴰ .⋆IdLᴰ = Cᴰ.⋆IdLᴰ
  ChangeOfObjectsᴰ .⋆IdRᴰ = Cᴰ.⋆IdRᴰ
  ChangeOfObjectsᴰ .⋆Assocᴰ = Cᴰ.⋆Assocᴰ
  ChangeOfObjectsᴰ .isSetHomᴰ = Cᴰ.isSetHomᴰ

  πᴰ : Functorⱽ ChangeOfObjectsᴰ Cᴰ
  πᴰ .F-obᴰ = F
  πᴰ .F-homᴰ fᴰ = fᴰ
  πᴰ .F-idᴰ = refl
  πᴰ .F-seqᴰ fᴰ gᴰ = refl

  open ChosenReind

  ChangeOfObjectsReind : ChosenReind Cᴰ → ChosenReind ChangeOfObjectsᴰ
  ChangeOfObjectsReind cr .reind⟨_⟩ = cr .reind⟨_⟩
  ChangeOfObjectsReind cr .reind-filler = cr .reind-filler
