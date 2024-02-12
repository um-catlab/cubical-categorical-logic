{-# OPTIONS --safe #-}
-- TODO this gets moved to Categories.Isomorphism
module Cubical.Categories.Displayed.Constructions.IsomorphismMore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level


module _ {C : Category ℓC ℓC'} where
  open Category C
  open isIso

  -- TODO Better names
  ⋆InvLMoveInv : {x y z : ob}
    (f : CatIso C x y)
    {g : Hom[ y , z ]}{h : Hom[ x , z ]}
    → g ≡ f .snd .inv ⋆ h
    → f .fst ⋆ g ≡ h
  ⋆InvLMoveInv f {g = g} {h = h} p =
    cong (λ a → f .fst ⋆⟨ C ⟩ a) p ∙
    sym (⋆Assoc _ _ _) ∙
    cong (λ a → a ⋆⟨ C ⟩ h) (f .snd .ret) ∙
    ⋆IdL _

  ⋆InvRMoveInv : {x y z : ob}
    (f : CatIso C y z)
    {g : Hom[ x , y ]}{h : Hom[ x , z ]}
    → g ≡ h ⋆ f .snd .inv
    → g ⋆ f .fst ≡ h
  ⋆InvRMoveInv f {g = g} {h = h} p =
    cong (λ a → a ⋆⟨ C ⟩ f .fst) p ∙
    ⋆Assoc _ _ _ ∙
    cong (λ a → h ⋆⟨ C ⟩ a) (f .snd .sec) ∙
    ⋆IdR _
