module Cubical.Categories.LocallySmall.Functor.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Section.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base

open Functor
module _ {C : Category Cob CHom-ℓ} {D : Category Dob DHom-ℓ} (d : Dob) where
  private
    module D = CategoryNotation D
  Constant : Functor C D
  Constant .F-ob _ = d
  Constant .F-hom _ = D.id
  Constant .F-id = refl
  Constant .F-seq _ _ = sym (D.⋆IdL _)

module _
  {C : Category Cob CHom-ℓ}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  (c : Cob) where
  private
    module C = CategoryNotation C
    module Cᴰ = CategoryᴰNotation Cᴰ

  ConstantSection : Section {D = Cᴰ.v[ c ]} (Constant c) Cᴰ
  ConstantSection .Section.F-obᴰ = λ d → d
  ConstantSection .Section.F-homᴰ = λ f → f
  ConstantSection .Section.F-idᴰ =
    sym $ Cᴰ.reind-filler _ _
  ConstantSection .Section.F-seqᴰ _ _ =
    sym $ Cᴰ.reind-filler _ _

  module _ (C-⋆ : ∀ {x} → C.id C.⋆ C.id Eq.≡ C.id {x}) where
    ConstantSectionEq : Section {D = fibEq Cᴰ C-⋆ c} (Constant c) Cᴰ
    ConstantSectionEq .Section.F-obᴰ = λ d → d
    ConstantSectionEq .Section.F-homᴰ = λ f → f
    ConstantSectionEq .Section.F-idᴰ = refl
    ConstantSectionEq .Section.F-seqᴰ f g =
      Eq.J
      (λ u v → (u , Eq.transport Cᴰ.Hom[_][ _ , _ ] v (f Cᴰ.⋆ᴰ g)) ≡
      (C.id C.⋆ C.id , f Cᴰ.⋆ᴰ g))
      refl
      C-⋆
