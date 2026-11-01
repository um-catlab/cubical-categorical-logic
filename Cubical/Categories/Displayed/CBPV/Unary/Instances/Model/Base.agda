-- Sets and Models of a Theory as a CBPV Model
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (l to 𝒱; r to 𝒞)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Instances.Algebra.DisplayedModel
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Model
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Displayed.FromU
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.FromU

open import Cubical.Algebra.Theory.Base

private
  variable
    ℓ ℓᴰ ℓO ℓA ℓE ℓEA : Level

open Category
open Functorᴰ

module _ (T : Theory ℓO ℓA ℓE ℓEA) where
  open Theory T

  private
    L = ModelLevel T

  ModelCBPVEq : MultCBPVCatEq (ℓ-suc L) L
  ModelCBPVEq = U→MultCBPVEq (MODELForget T) (MODELFree T)

  ModelCBPV : MultCBPVCat (ℓ-suc L) L
  ModelCBPV = forgetEq ModelCBPVEq

  ModelCBPVᴰ : CBPVCatᴰ (ModelCBPV .fst) (ℓ-suc L) L
  ModelCBPVᴰ = U→CBPVᴰ (MODELForget T) (MODELForgetᴰ T {ℓ = L} {ℓᴰ = L})

  ModelCBPVModel : ModelEnrichment (ModelCBPV .fst) T
  ModelCBPVModel .fst A B = PowerModel ⟨ A ⟩ B .snd
  ModelCBPVModel .snd .fst V B op γ op⟨γ⟩ p =
    λ i x → p i (V x)
  ModelCBPVModel .snd .snd S A op γ op⟨γ⟩ p =
    funExt λ x → S .snd op (λ v → γ v x) (op⟨γ⟩ x)
      (λ i → p i x)

  module _
    (C : CBPVCat ℓ L) (CModel : ModelEnrichment C T)
    (P : Fibers.ob[_] C 𝒱)
    where
    private module C = Fibers C

    points : Functorⱽ C (ModelCBPV .fst)
    points .F-obᴰ {x = 𝒱} A = C.Hom[ _ ][ P , A ] , C.isSetHomᴰ
    points .F-obᴰ {x = 𝒞} B =
      ((C.Hom[ _ ][ P , B ] , C.isSetHomᴰ) , CModel .fst P B)
    points .F-homᴰ {x = 𝒱} {y = 𝒱} f M = M C.⋆ᴰ f
    points .F-homᴰ {x = 𝒱} {y = 𝒞} f M = M C.⋆ᴰ f
    points .F-homᴰ {x = 𝒞} {y = 𝒞} f =
      (λ M → M C.⋆ᴰ f) , CModel .snd .snd f P
    points .F-idᴰ {x = 𝒱} = funExt C.⋆IdRᴰ
    points .F-idᴰ {x = 𝒞} =
      Σ≡Prop (λ _ → isPropΠ4 λ _ _ _ _ → C.isSetHomᴰ _ _)
        (funExt C.⋆IdRᴰ)
    points .F-seqᴰ {x = 𝒱} {y = 𝒱} {z = 𝒱} f g =
      funExt λ M → sym (C.⋆Assocᴰ M f g)
    points .F-seqᴰ {x = 𝒱} {y = 𝒱} {z = 𝒞} f g =
      funExt λ M → sym (C.⋆Assocᴰ M f g)
    points .F-seqᴰ {x = 𝒱} {y = 𝒞} {z = 𝒞} f g =
      funExt λ M → sym (C.⋆Assocᴰ M f g)
    points .F-seqᴰ {x = 𝒞} {y = 𝒞} {z = 𝒞} f g =
      Σ≡Prop (λ _ → isPropΠ4 λ _ _ _ _ → C.isSetHomᴰ _ _)
        (funExt λ M → sym (C.⋆Assocᴰ M f g))

    pointsPreservesModel :
      PreservesModelEnrichment T points CModel ModelCBPVModel
    pointsPreservesModel A B op γ op⟨γ⟩ p =
      funExt λ V → CModel .snd .fst V B op γ op⟨γ⟩ p

    -- Points always preserves a value (or computation) terminal object
    pointsPreserveTerminal : (term : Terminalⱽ C 𝒱)
      → Iso ⟨ points .F-obᴰ (term .fst) ⟩ (Unit* {L})
    pointsPreserveTerminal term = isom
      where
      module Term = RepresentableⱽNotation C 𝒱 UnitPshᴰ term
      isom : Iso ⟨ points .F-obᴰ (term .fst) ⟩ (Unit* {L})
      isom .Iso.fun _ = tt*
      isom .Iso.inv _ = Term.introⱽ tt
      isom .Iso.sec _ = refl
      isom .Iso.ret V = sym (C.rectify {e' = refl} (C.≡out (Term.∫ηⱽ V)))

  ModelCBPVModelᴰ : ModelEnrichmentᴰ T ModelCBPVModel ModelCBPVᴰ
  ModelCBPVModelᴰ .fst {A = A} {B = B} Aᴰ Bᴰ =
    PowerModelᴰ ⟨ A ⟩ B (λ x → ⟨ Aᴰ x ⟩) Bᴰ .snd
  ModelCBPVModelᴰ .snd .fst {V = V} Vᴰ
    op γ γᴰ op⟨γ⟩ p op⟨γᴰ⟩ pᴰ i x xᴰ =
      pᴰ i (V x) (Vᴰ x xᴰ)
  ModelCBPVModelᴰ .snd .snd {S = S} Sᴰ
    op γ γᴰ op⟨γ⟩ p op⟨γᴰ⟩ pᴰ i x xᴰ =
      Sᴰ .snd op (λ v → γ v x) (λ v → γᴰ v x xᴰ)
        (op⟨γ⟩ x) (λ j → p j x)
        (op⟨γᴰ⟩ x xᴰ) (λ j → pᴰ j x xᴰ) i
