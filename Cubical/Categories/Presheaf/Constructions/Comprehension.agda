{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.Comprehension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.Presheaf.Base

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓP ℓQ ℓS : Level

module _ {C : Category ℓ ℓ'} where

  open Functor
  open Functorᴰ
  module _ (P : Presheaf C ℓA) (Pᴰ : Presheafᴰ P (Unitᴰ _) ℓB) where
    private
      module C = Category C
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
    ΣPsh :  Presheaf C (ℓ-max ℓA ℓB)
    ΣPsh .F-ob x .fst = Σ[ p ∈ P.p[ x ] ] ⟨ Pᴰ .F-obᴰ _ p ⟩
    ΣPsh .F-ob x .snd = isSetΣ P.isSetPsh (λ p → Pᴰ .F-obᴰ _ _ .snd)
    ΣPsh .F-hom f (p , pᴰ) = _ , Pᴰ .F-homᴰ {f = f} _ p pᴰ
    ΣPsh .F-id = funExt λ (p , pᴰ) →
      ΣPathP (_ , λ i → Pᴰ .F-idᴰ i p pᴰ )
    ΣPsh .F-seq f g = funExt λ (p , pᴰ) →
      ΣPathP (_ , λ i → Pᴰ .F-seqᴰ {f = f}{g = g} _ _ i p pᴰ)

    -- Γ , x: p
    Comprehension : (Γ : C.ob) → P.p[ Γ ] → Presheaf C (ℓ-max ℓ' ℓB)
    Comprehension Γ p .F-ob Δ .fst =
      Σ[ γ ∈ C [ Δ , Γ ] ] Pᴰ.p[ γ P.⋆ p ][ _ ]
    Comprehension Γ p .F-ob Δ .snd = isSetΣ C.isSetHom (λ _ → Pᴰ.isSetPshᴰ)
    Comprehension Γ p .F-hom δ (γ , pᴰ) =
      (δ C.⋆ γ) , Pᴰ.reind {e = sym $ P.⋆Assoc _ _ _}
        (_ Pᴰ.⋆ᴰ pᴰ)
    Comprehension Γ p .F-id = funExt (λ (γ , q) → ΣPathP ((C.⋆IdL _) ,
      (Pᴰ.rectify $ Pᴰ.≡out $
        sym (Pᴰ.reind-filler)
        ∙ Pᴰ.⋆IdL _)))
    Comprehension Γ p .F-seq f g = funExt λ (γ , q) → ΣPathP (C.⋆Assoc _ _ _
      , (Pᴰ.rectify $ Pᴰ.≡out $
        sym (Pᴰ.reind-filler)
        ∙ Pᴰ.⋆Assoc _ _ _
        ∙ Pᴰ.⟨ refl ⟩⋆⟨ Pᴰ.reind-filler ⟩
        ∙ Pᴰ.reind-filler))
