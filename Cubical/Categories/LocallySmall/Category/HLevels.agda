module Cubical.Categories.LocallySmall.Category.HLevels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.LocallySmall.Variables.Base
open import Cubical.Categories.LocallySmall.Category.Base

module _ (C : Category Cob CHom-ℓ) where
  private
    module C = Category C
  hasContrHoms : Typeω
  hasContrHoms = ∀ (c c' : Cob) → isContr C.Hom[ c , c' ]

  module _ (contrHoms : hasContrHoms) (c c' : Cob) where
    open CatIso
    mkContrHomsIso : CatIso C c c'
    mkContrHomsIso .fun = contrHoms c c' .fst
    mkContrHomsIso .inv = contrHoms c' c .fst
    mkContrHomsIso .sec = sym (contrHoms c' c' .snd _) ∙ contrHoms c' c' .snd C.id
    mkContrHomsIso .ret = sym (contrHoms c c .snd _) ∙ contrHoms c c .snd C.id
