module Cubical.Categories.Category.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base

private
  variable
    ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} where
  private
    module C = Category C
  module _ {a b c : C.ob} where
    _⋆CatIso_ : CatIso C a b → CatIso C b c → CatIso C a c
    (α ⋆CatIso β) .fst = α .fst C.⋆ β .fst
    (α ⋆CatIso β) .snd .isIso.inv = β .snd .isIso.inv C.⋆ α .snd .isIso.inv
    (α ⋆CatIso β) .snd .isIso.sec =
      C.⋆Assoc _ _ _
      ∙ cong₂ C._⋆_ refl (sym (C.⋆Assoc _ _ _)
                          ∙ cong₂ C._⋆_ (α .snd .isIso.sec) refl
                          ∙ C.⋆IdL _)
      ∙ β .snd .isIso.sec
    (α ⋆CatIso β) .snd .isIso.ret =
      sym (C.⋆Assoc _ _ _)
      ∙ cong₂ C._⋆_ (C.⋆Assoc _ _ _ ∙ cong₂ C._⋆_ refl (β .snd .isIso.ret) ∙ C.⋆IdR _) refl
      ∙ α .snd .isIso.ret

    infixr 9 _⋆CatIso_

  step-CatIso : (a : C.ob) {b c : C.ob} → CatIso C b c → CatIso C a b → CatIso C a c
  step-CatIso _ g f = f ⋆CatIso g

  infixr  2 step-CatIso
  syntax step-CatIso a b f = a CatIso⟨ f ⟩ b

  _∎CatIso : ∀ (c : C.ob) → CatIso C c c
  c ∎CatIso = idCatIso

  infix   3 _∎CatIso
