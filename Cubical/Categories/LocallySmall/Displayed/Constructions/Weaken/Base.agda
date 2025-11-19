module Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Variables

open Category
open Categoryᴰ
open Σω

module _ (C : Category Cob CHom-ℓ)(D : Category Dob DHom-ℓ) where
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
  weaken : Categoryᴰ C (λ _ → Dob) _
  weaken .Hom[_][_,_] = λ _ → D.Hom[_,_]
  weaken .idᴰ = D.id
  weaken ._⋆ᴰ_ = D._⋆_
  weaken .⋆IdLᴰ = λ f → ≡-× (C.⋆IdL _) (D.⋆IdL f)
  weaken .⋆IdRᴰ = λ f → ≡-× (C.⋆IdR _) (D.⋆IdR f)
  weaken .⋆Assocᴰ = λ f g h → ≡-× (C.⋆Assoc _ _ _) (D.⋆Assoc f g h)
  weaken .isSetHomᴰ = D.isSetHom
