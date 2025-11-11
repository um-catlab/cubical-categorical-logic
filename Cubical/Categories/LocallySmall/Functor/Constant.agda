module Cubical.Categories.LocallySmall.Functor.Constant where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor

open Functor
module _ {C : Category Cob CHom-ℓ} {D : Category Dob DHom-ℓ} (d : Dob) where
  private
    module D = CategoryNotation D
  Constant : Functor C D
  Constant .F-ob _ = d
  Constant .F-hom _ = D.id
  Constant .F-id = refl
  Constant .F-seq _ _ = sym (D.⋆IdL _)
