{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (l to 𝒱; r to 𝒞)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Instances.Algebra.DisplayedModel
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Model
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Displayed.FromU
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.FromU

open import Cubical.Algebra.Theory.Base
  hiding (ℓ; ℓᴰ; ℓᴰᴰ; ℓ'; ℓᴰ'; ℓᴰᴰ'; ℓ''; ℓᴰ''; ℓO; ℓA; ℓE)

private
  variable
    ℓ ℓᴰ ℓO ℓA ℓE ℓEA : Level

open Category
open Functorᴰ

module _ (T : Theory ℓO ℓA ℓE ℓEA) where
  open Theory T

  private
    L = ModelLevel T

  ModelCBPVEqWithFree : LeftAdjoint (MODELForget T)
    → MultCBPVCatEq (ℓ-suc L) L
  ModelCBPVEqWithFree = U→MultCBPVEq (MODELForget T)

  ModelCBPVWithFree : LeftAdjoint (MODELForget T)
    → MultCBPVCat (ℓ-suc L) L
  ModelCBPVWithFree Free = forgetEq (ModelCBPVEqWithFree Free)

  ModelCBPVEq : MultCBPVCatEq (ℓ-suc L) L
  ModelCBPVEq = ModelCBPVEqWithFree (MODELFree T)

  ModelCBPV : MultCBPVCat (ℓ-suc L) L
  ModelCBPV = ModelCBPVWithFree (MODELFree T)

  MODELForgetᴰ : Functorᴰ (MODELForget T) (MODELᴰ T L L) (SETᴰ L L)
  MODELForgetᴰ .F-obᴰ Bᴰ = Bᴰ .fst
  MODELForgetᴰ .F-homᴰ fᴰ = fᴰ .fst
  MODELForgetᴰ .F-idᴰ = refl
  MODELForgetᴰ .F-seqᴰ _ _ = refl

  ModelCBPVᴰWithFree : (Free : LeftAdjoint (MODELForget T)) →
    CBPVCatᴰ (ModelCBPVWithFree Free .fst) (ℓ-suc L) L
  ModelCBPVᴰWithFree Free =
    U→CBPVᴰ (MODELForget T) MODELForgetᴰ

  ModelCBPVᴰ : CBPVCatᴰ (ModelCBPV .fst) (ℓ-suc L) L
  ModelCBPVᴰ = ModelCBPVᴰWithFree (MODELFree T)

  private
    HomAlgebra : (A : hSet L) (B : MODEL T L .ob) → Algebra L
    HomAlgebra A B .fst = ⟨ A ⟩ → ⟨ B .fst ⟩
    HomAlgebra A B .snd op γ x = B .snd .fst op (λ v → γ v x)

    evalHomo : (A : hSet L) (B : MODEL T L .ob) (x : ⟨ A ⟩)
      → Homo (HomAlgebra A B) (_ , B .snd .fst)
    evalHomo A B x .fst f = f x
    evalHomo A B x .snd op γ op⟨γ⟩ p i = p i x

    HomIsModel : (A : hSet L) (B : MODEL T L .ob)
      → IsModel (HomAlgebra A B)
    HomIsModel A B e γ = funExt λ x →
      sym (interpHomo (evalHomo A B x) γ (lhs e))
      ∙ B .snd .snd e (λ v → γ v x)
      ∙ interpHomo (evalHomo A B x) γ (rhs e)

    HomModel : (A : hSet L) (B : MODEL T L .ob) → Model L
    HomModel A B .fst = HomAlgebra A B
    HomModel A B .snd .fst = HomIsModel A B
    HomModel A B .snd .snd = isSetΠ λ _ → B .fst .snd

    HomAlgebraᴰ : (A : hSet L) (B : MODEL T L .ob)
      (Aᴰ : ⟨ A ⟩ → hSet L)
      (Bᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) B)
      → Algebraᴰ (HomAlgebra A B) L
    HomAlgebraᴰ A B Aᴰ Bᴰ .fst f =
      (x : ⟨ A ⟩) → ⟨ Aᴰ x ⟩ → ⟨ Bᴰ .fst (f x) ⟩
    HomAlgebraᴰ A B Aᴰ Bᴰ .snd
      op γ γᴰ op⟨γ⟩ p x xᴰ =
        Bᴰ .snd .fst op (λ v → γ v x) (λ v → γᴰ v x xᴰ)
          (op⟨γ⟩ x) (λ i → p i x)

    interpHomᴰAt : (A : hSet L) (B : MODEL T L .ob)
      (Aᴰ : ⟨ A ⟩ → hSet L)
      (Bᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) B)
      {V : Type ℓ}
      (ρ : V → HomAlgebra A B .fst)
      (ρᴰ : (v : V) → HomAlgebraᴰ A B Aᴰ Bᴰ .fst (ρ v))
      (t : |FreeAlgebra| V) (x : ⟨ A ⟩) (xᴰ : ⟨ Aᴰ x ⟩)
      → interpᴰ (HomAlgebraᴰ A B Aᴰ Bᴰ) ρ ρᴰ t x xᴰ
        ≡ interpᴰ
            (evalHomo A B x S.* (_ , Bᴰ .snd .fst))
            ρ (λ v → ρᴰ v x xᴰ) t
    interpHomᴰAt A B Aᴰ Bᴰ ρ ρᴰ (var v) x xᴰ = refl
    interpHomᴰAt A B Aᴰ Bᴰ ρ ρᴰ (app op γ) x xᴰ =
      cong
        (λ γᴰ → Bᴰ .snd .fst op
          (λ v → interp (HomAlgebra A B) ρ (γ v) x) γᴰ
          (interp (HomAlgebra A B) ρ (app op γ) x)
          (λ i → recFA (HomAlgebra A B) ρ .snd
            op γ (app op γ) refl i x))
        (funExt λ v → interpHomᴰAt A B Aᴰ Bᴰ ρ ρᴰ (γ v) x xᴰ)

  ModelCBPVModel : ModelEnrichment (ModelCBPV .fst) T
  ModelCBPVModel .fst A B .fst = HomModel A B .fst .snd
  ModelCBPVModel .fst A B .snd = HomModel A B .snd .fst
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

  ModelCBPVModelᴰ : ModelEnrichmentᴰ T ModelCBPVModel ModelCBPVᴰ
  ModelCBPVModelᴰ .fst {A = A} {B = B} Aᴰ Bᴰ .fst =
    HomAlgebraᴰ A B Aᴰ Bᴰ .snd
  ModelCBPVModelᴰ .fst {A = A} {B = B} Aᴰ Bᴰ .snd e ρ ρᴰ i x xᴰ =
    hSetReasoning.rectifyOut (B .fst) (λ b → ⟨ Bᴰ .fst b ⟩)
      {e' = cong (λ f → f x) (HomIsModel A B e ρ)}
      ( (λ j →
          interp (HomAlgebra A B) ρ (lhs e) x
          , interpHomᴰAt A B Aᴰ Bᴰ ρ ρᴰ (lhs e) x xᴰ j)
      ∙ sym (interpPullback (evalHomo A B x)
          (_ , Bᴰ .snd .fst) ρ (λ v → ρᴰ v x xᴰ) (lhs e))
      ∙ ΣPathP
          ( B .snd .snd e (λ v → ρ v x)
          , Bᴰ .snd .snd e (λ v → ρ v x)
              (λ v → ρᴰ v x xᴰ))
      ∙ interpPullback (evalHomo A B x)
          (_ , Bᴰ .snd .fst) ρ (λ v → ρᴰ v x xᴰ) (rhs e)
      ∙ (λ j →
          interp (HomAlgebra A B) ρ (rhs e) x
          , interpHomᴰAt A B Aᴰ Bᴰ ρ ρᴰ (rhs e) x xᴰ (~ j))) i
  ModelCBPVModelᴰ .snd .fst {V = V} Vᴰ
    op γ γᴰ op⟨γ⟩ p op⟨γᴰ⟩ pᴰ i x xᴰ =
      pᴰ i (V x) (Vᴰ x xᴰ)
  ModelCBPVModelᴰ .snd .snd {S = S} Sᴰ
    op γ γᴰ op⟨γ⟩ p op⟨γᴰ⟩ pᴰ i x xᴰ =
      Sᴰ .snd op (λ v → γ v x) (λ v → γᴰ v x xᴰ)
        (op⟨γ⟩ x) (λ j → p j x)
        (op⟨γᴰ⟩ x xᴰ) (λ j → pᴰ j x xᴰ) i
