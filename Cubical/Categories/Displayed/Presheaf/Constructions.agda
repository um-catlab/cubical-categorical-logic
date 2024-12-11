{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Presheaf.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Bifunctor.Redundant

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open Category
open NatTrans
open Functorᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  PshProdᴰ : {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
             (Pᴰ : Presheafᴰ Cᴰ P ℓPᴰ) (Qᴰ : Presheafᴰ Cᴰ Q ℓQᴰ)
           → Presheafᴰ Cᴰ (PshProd ⟅ P , Q ⟆b) (ℓ-max ℓPᴰ ℓQᴰ)
  PshProdᴰ Pᴰ Qᴰ .F-obᴰ xᴰ (p , q) .fst =
    ⟨ Pᴰ .F-obᴰ xᴰ p ⟩ × ⟨ Qᴰ .F-obᴰ xᴰ q ⟩
  PshProdᴰ Pᴰ Qᴰ .F-obᴰ xᴰ (p , q) .snd =
    isSet× (Pᴰ .F-obᴰ xᴰ p .snd) (Qᴰ .F-obᴰ xᴰ q .snd)
  PshProdᴰ Pᴰ Qᴰ .F-homᴰ fᴰ (p , q) (pᴰ , qᴰ) .fst = Pᴰ .F-homᴰ fᴰ p pᴰ
  PshProdᴰ Pᴰ Qᴰ .F-homᴰ fᴰ (p , q) (pᴰ , qᴰ) .snd = Qᴰ .F-homᴰ fᴰ q qᴰ
  PshProdᴰ Pᴰ Qᴰ .F-idᴰ = funExt (λ (p , q) → funExt λ (pᴰ , qᴰ) →
    ΣPathP ( funExt⁻ (funExt⁻ (Pᴰ .F-idᴰ) p) pᴰ
           , (funExt⁻ (funExt⁻ (Qᴰ .F-idᴰ) q) qᴰ)))
  PshProdᴰ Pᴰ Qᴰ .F-seqᴰ fᴰ gᴰ =
     funExt (λ (p , q) → funExt λ (pᴰ , qᴰ) → ΣPathP
       ( (funExt⁻ (funExt⁻ (Pᴰ .F-seqᴰ fᴰ gᴰ) p) pᴰ)
       , (funExt⁻ (funExt⁻ (Qᴰ .F-seqᴰ fᴰ gᴰ) q) qᴰ)))

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
           (Qᴰ : Presheafᴰ Cᴰ Q ℓQᴰ)
           (α : PshHomⱽ P Q) where
    private
      module Qᴰ = PresheafᴰReasoning Qᴰ
    PshReind : Presheafᴰ Cᴰ P ℓQᴰ
    PshReind .F-obᴰ xᴰ p = Qᴰ .F-obᴰ xᴰ $ α .fst _ p
    PshReind .F-homᴰ fᴰ p qᴰ = Qᴰ.reind (sym $ α .snd _ _) (fᴰ Qᴰ.⋆ᴰ qᴰ)
    PshReind .F-idᴰ = funExt₂ λ p qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      (sym $ Qᴰ.reind-filler _ _)
      ∙ Qᴰ.⋆ᴾId _
    PshReind .F-seqᴰ fᴰ gᴰ = funExt₂ λ p qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      (sym $ Qᴰ.reind-filler _ _)
      ∙ (Qᴰ.≡in $ (λ i → Qᴰ .F-seqᴰ fᴰ gᴰ i _ qᴰ))
      ∙ Qᴰ.⟨ refl ⟩⋆ᴾ⟨ Qᴰ.reind-filler _ _ ⟩
      ∙ Qᴰ.reind-filler _ _
