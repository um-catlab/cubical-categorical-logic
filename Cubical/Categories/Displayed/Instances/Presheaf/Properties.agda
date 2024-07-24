{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws
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
open import Cubical.Categories.Displayed.Instances.Presheaf

open Category
open Functor
open Categoryᴰ
open Contravariant
open NatTrans

private
  variable ℓA ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓSET : Level

module _ (C : Category ℓC ℓC') (ℓS : Level) where
  open UniversalElementᴰ
  open CartesianOver
  -- TODO: fix levels
  PRESHEAFᴰ-fibration : isFibration (PRESHEAFᴰ C ℓ-zero ℓS)
  PRESHEAFᴰ-fibration {d = Q} (P , Pᴰ , α) = CartesianOver→CartesianLift
    (PRESHEAFᴰ C ℓ-zero ℓS)
    co
    where
    co : CartesianOver (PRESHEAFᴰ C ℓ-zero ℓS) Pᴰ α
    co .f*cᴰ' .F-ob (Γ , ϕ) = Pᴰ ⟅ Γ , (α ⟦ Γ ⟧) ϕ ⟆
    co .f*cᴰ' .F-hom {x = Γ,ϕ} {y = Δ,ψ} (f , p) = Pᴰ ⟪ f ,
      sym (funExt⁻ (α .N-hom f) (Γ,ϕ .snd)) ∙
      congS (α ⟦ Δ,ψ .fst ⟧) p ⟫
    co .f*cᴰ' .F-id {x = Γ , ϕ} = funExt (λ α⟦Γ⟧ϕᴰ →
      congS (λ x → (Pᴰ ⟪ C .id , x ⟫) α⟦Γ⟧ϕᴰ) ((P ⟅ _ ⟆) .snd _ _ _ _) ∙
      funExt⁻ (Pᴰ .F-id) α⟦Γ⟧ϕᴰ)
    co .f*cᴰ' .F-seq (f , p) (g , q) =
      congS (λ x → Pᴰ ⟪ x ⟫) (ΣPathP (refl , ((P ⟅ _ ⟆) .snd _ _ _ _))) ∙
      Pᴰ .F-seq _ _
    co .π = natTrans (λ _ → idfun _) (λ _ → refl)
    co .isCartesian {c'' = R} Rᴰ β βαᴰ = uniqueExists
      (natTrans (βαᴰ ⟦_⟧) (λ _ → funExt (λ ϕᴰ →
        funExt⁻ (βαᴰ .N-hom _) ϕᴰ ∙
        congS (λ x → (Pᴰ ⟪ x ⟫) ((βαᴰ ⟦ _ ⟧) ϕᴰ))
          (ΣPathP (refl , (P ⟅ _ ⟆) .snd _ _ _ _)))))
      (makeNatTransPath refl)
      (λ _ → isSetNatTrans _ _)
      (λ _ p → makeNatTransPath (sym (congS N-ob p)))
