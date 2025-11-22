{-

  Given a category C and a function X → C .ob, make a new category
  whose objects are X and morphisms are given by C.

  This is useful for cleaning up compositional constructions that end
  up with useless data in the objects like X × 1.

-}
module Cubical.Categories.LocallySmall.Displayed.Constructions.ChangeOfObjects where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Constructions.ChangeOfObjects

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Category

module _ where
  open CategoryᴰVariables
  module ChangeOfObjectsᴰ
    {X : Typeω}
    {Y : X → Typeω}
    (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ) where
    private
      module C = CategoryNotation C
      module Cᴰ = Categoryᴰ Cᴰ
    module _ {F : X → C.Ob} (Fᴰ : ∀ {x : X} → Y x → Cobᴰ (F x)) where
      ChangeOfObjectsᴰ : Categoryᴰ (ChangeOfObjects C F) _ _
      ChangeOfObjectsᴰ .Categoryᴰ.Hom[_][_,_] f xᴰ yᴰ = Cᴰ.Hom[ f ][ Fᴰ xᴰ , Fᴰ yᴰ ]
      ChangeOfObjectsᴰ .Categoryᴰ.idᴰ = Cᴰ.idᴰ
      ChangeOfObjectsᴰ .Categoryᴰ._⋆ᴰ_ = Cᴰ._⋆ᴰ_
      ChangeOfObjectsᴰ .Categoryᴰ.⋆IdLᴰ = Cᴰ.⋆IdLᴰ
      ChangeOfObjectsᴰ .Categoryᴰ.⋆IdRᴰ = Cᴰ.⋆IdRᴰ
      ChangeOfObjectsᴰ .Categoryᴰ.⋆Assocᴰ = Cᴰ.⋆Assocᴰ
      ChangeOfObjectsᴰ .Categoryᴰ.isSetHomᴰ = Cᴰ.isSetHomᴰ

      open Functorᴰ
      πᴰ : Functorᴰ (π C F) ChangeOfObjectsᴰ Cᴰ
      πᴰ .F-obᴰ = Fᴰ
      πᴰ .F-homᴰ = λ fᴰ → fᴰ
      πᴰ .F-idᴰ = refl
      πᴰ .F-seqᴰ = λ _ _ → refl

  module ChangeOfDisplayedObjectsᴰ
    (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
    where
    private
      module C = CategoryNotation C
      module Cᴰ = Categoryᴰ Cᴰ
    module _ {Y : C.Ob → Typeω}
      (Fᴰ : ∀ {x : C.Ob} → Y x → Cobᴰ x) where
      ChangeOfObjectsᴰ : Categoryᴰ C _ _
      ChangeOfObjectsᴰ .Categoryᴰ.Hom[_][_,_] f xᴰ yᴰ = Cᴰ.Hom[ f ][ Fᴰ xᴰ , Fᴰ yᴰ ]
      ChangeOfObjectsᴰ .Categoryᴰ.idᴰ = Cᴰ.idᴰ
      ChangeOfObjectsᴰ .Categoryᴰ._⋆ᴰ_ = Cᴰ._⋆ᴰ_
      ChangeOfObjectsᴰ .Categoryᴰ.⋆IdLᴰ = Cᴰ.⋆IdLᴰ
      ChangeOfObjectsᴰ .Categoryᴰ.⋆IdRᴰ = Cᴰ.⋆IdRᴰ
      ChangeOfObjectsᴰ .Categoryᴰ.⋆Assocᴰ = Cᴰ.⋆Assocᴰ
      ChangeOfObjectsᴰ .Categoryᴰ.isSetHomᴰ = Cᴰ.isSetHomᴰ

      open Functorᴰ
      πᴰ : Functorⱽ ChangeOfObjectsᴰ Cᴰ
      πᴰ .F-obᴰ = Fᴰ
      πᴰ .F-homᴰ = λ fᴰ → fᴰ
      πᴰ .F-idᴰ = refl
      πᴰ .F-seqᴰ = λ _ _ → refl
