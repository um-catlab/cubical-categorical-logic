module Cubical.Categories.LocallySmall.Instances.Weaken where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Instances.Unit

open import Cubical.Categories.LocallySmall.Displayed.Category.Base

open Categoryᴰ

module _ (C : Category Cob CHom-ℓ) where
  private
    module C = CategoryNotation C
  weaken : Categoryᴰ UNIT (λ _ → Cob) λ _ _ → CHom-ℓ
  weaken .Hom[_][_,_] _ = C.Hom[_,_]
  weaken .idᴰ = C.id
  weaken ._⋆ᴰ_ = C._⋆_
  weaken .⋆IdLᴰ fᴰ = ΣPathP (refl , (C.⋆IdL fᴰ))
  weaken .⋆IdRᴰ fᴰ = ΣPathP (refl , (C.⋆IdR fᴰ))
  weaken .⋆Assocᴰ fᴰ gᴰ hᴰ = ΣPathP (refl , C.⋆Assoc fᴰ gᴰ hᴰ)
  weaken .isSetHomᴰ = C.isSetHom
