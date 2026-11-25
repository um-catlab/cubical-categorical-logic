module Cubical.Categories.Isomorphism.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Isomorphism

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open isIso
module _ {C : Category ℓC ℓC'} where
  ⋆InvLMove⁻ : {x y z : C .ob}
    (f : CatIso C x y)
    {g : C [ y , z ]}{h : C [ x , z ]}
    → g ≡ f .snd .inv ⋆⟨ C ⟩ h
    → f .fst ⋆⟨ C ⟩ g ≡ h
  ⋆InvLMove⁻ f {g = g} {h = h} p =
    cong (λ a → f .fst ⋆⟨ C ⟩ a) p ∙
    sym (C .⋆Assoc _ _ _) ∙
    cong (λ a → a ⋆⟨ C ⟩ h) (f .snd .ret) ∙
    C .⋆IdL _

  ⋆InvRMove⁻ : {x y z : C .ob}
    (f : CatIso C y z)
    {g : C [ x , y ]}{h : C [ x , z ]}
    → g ≡ h ⋆⟨ C ⟩ f .snd .inv
    → g ⋆⟨ C ⟩ f .fst ≡ h
  ⋆InvRMove⁻ f {g = g} {h = h} p =
    cong (λ a → a ⋆⟨ C ⟩ f .fst) p ∙
    C .⋆Assoc _ _ _ ∙
    cong (λ a → h ⋆⟨ C ⟩ a) (f .snd .sec) ∙
    C .⋆IdR _

  ⋆InvsFlipSq : {w x y z : C .ob}
    (e : CatIso C w x)
    {g : C [ w , y ]}
    {h : C [ x , z ]}
    (f : CatIso C y z)
    → e .fst ⋆⟨ C ⟩ h ≡ g ⋆⟨ C ⟩ f .fst
    → h ⋆⟨ C ⟩ f .snd .inv ≡ e .snd .inv ⋆⟨ C ⟩ g
  ⋆InvsFlipSq e {g} {h} f p =
    ⋆InvLMove e
      (sym (C .⋆Assoc _ _ _)
      ∙ sym (⋆InvRMove f (sym p)))

  ⋆InvsFlipSq⁻ : {w x y z : C .ob}
    (e : CatIso C w x)
    {g : C [ w , y ]}
    {h : C [ x , z ]}
    (f : CatIso C y z)
    → h ⋆⟨ C ⟩ f .snd .inv ≡ e .snd .inv ⋆⟨ C ⟩ g
    → e .fst ⋆⟨ C ⟩ h ≡ g ⋆⟨ C ⟩ f .fst
  ⋆InvsFlipSq⁻ e f p = ⋆InvLMove⁻ e
    ( sym (⋆InvRMove⁻ f (sym p))
    ∙ C .⋆Assoc _ _ _)

module _ {C : Category ℓC ℓC'} where
  private
    module C = Category C

  step-CatIso : (a : C.ob) {b c : C.ob} → CatIso C b c → CatIso C a b → CatIso C a c
  step-CatIso _ g f = ⋆Iso f g

  infixr  2 step-CatIso
  syntax step-CatIso a b f = a CatIso⟨ f ⟩ b

  _∎CatIso : ∀ (c : C.ob) → CatIso C c c
  c ∎CatIso = idCatIso

  infix   3 _∎CatIso

module _ {C : Category ℓC ℓC'} {x y : C .ob} (f : CatIso C x y)
  (f' : singl (f .fst)) (f⁻ : singl (f .snd .inv)) where
  improveCatIso : CatIso C x y
  improveCatIso .fst = f' .fst
  improveCatIso .snd .inv = f⁻ .fst
  improveCatIso .snd .sec =
    subst2 (λ g g⁻ → g⁻ ⋆⟨ C ⟩ g ≡ C .id) (f' .snd) (f⁻ .snd) (f .snd .sec)
  improveCatIso .snd .ret =
    subst2 (λ g g⁻ → g ⋆⟨ C ⟩ g⁻ ≡ C .id) (f' .snd) (f⁻ .snd) (f .snd .ret)
