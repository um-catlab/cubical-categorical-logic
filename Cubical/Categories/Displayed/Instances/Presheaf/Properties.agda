{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.CCC

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf using (UniversalElementᴰ)
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Base

open Category
open Functor
open NatTrans
open Contravariant
open Categoryᴰ
open UniversalElementᴰ

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓS ℓSᴰ : Level

open CartesianLift
module _ (C : Category ℓC ℓC') where
  reindPresheafᴰ : ∀ {P : Presheaf C ℓS}{Q : Presheaf C ℓS}
    (α : PresheafCategory C ℓS [ P , Q ])
    (Pᴰ : Presheafᴰ C ℓS ℓSᴰ Q)
    → Presheafᴰ C ℓS ℓSᴰ P
  reindPresheafᴰ α Pᴰ .F-ob (Γ , ϕ) = Pᴰ ⟅ Γ , (α ⟦ Γ ⟧) ϕ ⟆
  reindPresheafᴰ α Pᴰ .F-hom {x = Γ,ϕ} {y = Δ,ψ} (f , p) =
    Pᴰ ⟪ f , sym (funExt⁻ (α .N-hom f) (Γ,ϕ .snd)) ∙ congS (α ⟦ Δ,ψ .fst ⟧) p ⟫
  reindPresheafᴰ {Q = Q} α Pᴰ .F-id {x = Γ , ϕ} =
    funExt (λ α⟦Γ⟧ϕᴰ →
      congS (λ x → (Pᴰ ⟪ C .id , x ⟫) α⟦Γ⟧ϕᴰ) ((Q ⟅ _ ⟆) .snd _ _ _ _) ∙
      funExt⁻ (Pᴰ .F-id) α⟦Γ⟧ϕᴰ)
  reindPresheafᴰ {Q = Q} α Pᴰ .F-seq _ _ =
    congS (λ x → Pᴰ ⟪ _ , x ⟫) ((Q ⟅ _ ⟆) .snd _ _ _ _) ∙
    Pᴰ .F-seq _ _
module _ (C : Category ℓC ℓC') (ℓS ℓSᴰ : Level) where
  opaque
    isFibrationPRESHEAFᴰ : isFibration (PRESHEAFᴰ C ℓS ℓSᴰ)
    isFibrationPRESHEAFᴰ Pᴰ α .f*yᴰ = reindPresheafᴰ C α Pᴰ
    isFibrationPRESHEAFᴰ Pᴰ α .π = natTrans (λ x z → z) (λ _ → refl)
    isFibrationPRESHEAFᴰ {c' = Q} Pᴰ α .isCartesian {g = β} .fst  βαᴰ =
      natTrans (βαᴰ ⟦_⟧) (λ _ → funExt (λ ϕᴰ →
      funExt⁻ (βαᴰ .N-hom _) ϕᴰ ∙
      congS (λ x → (Pᴰ ⟪ _ , x ⟫) ((βαᴰ ⟦ _ ⟧) ϕᴰ))
        ((Q ⟅ _ ⟆) .snd _ _ _ _)))
    isFibrationPRESHEAFᴰ Pᴰ α .isCartesian {g = β} .snd .fst βαᴰ =
      makeNatTransPath refl
    isFibrationPRESHEAFᴰ Pᴰ α .isCartesian {g = β} .snd .snd αᴰ =
      makeNatTransPath refl
