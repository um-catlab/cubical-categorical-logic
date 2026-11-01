-- Multiplicative structure for the Set/Model unary CBPV model.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Multiplicative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq

open import Cubical.Algebra.Theory.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (l to 𝒱; r to 𝒞)
import Cubical.Categories.Instances.WalkingArrow as WA
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Instances.Algebra.DisplayedModel
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.FromU
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Base

private
  variable
    ℓX ℓO ℓA ℓE ℓEA : Level

module _ (T : Theory ℓO ℓA ℓE ℓEA) where
  open Theory T

  private
    L = ModelLevel T
    C = ModelCBPV T .fst
    Cᴰ = ModelCBPVᴰ T

    open U→CBPVEqLaws (MODELForget T {ℓ = L})
      (λ _ → Eq.refl) (λ _ → Eq.refl) (λ _ _ _ → Eq.refl)
      (λ _ → Eq.refl) (λ _ → Eq.refl) (λ _ _ _ → Eq.refl)
      (λ _ → Eq.refl) (λ _ _ _ → Eq.refl)
      using () renaming (idR to CBPVIdR; assoc to CBPVAssoc;
        idR^op to CBPVIdR^op; assoc^op to CBPVAssoc^op)

    CBPVIdRᵒᵖ : EqPsh.EqIdR (∫C (C ^opᴰ))
    CBPVIdRᵒᵖ = CBPVIdR^op

    CBPVAssocᵒᵖ : EqPsh.ReprEqAssoc (∫C (C ^opᴰ))
    CBPVAssocᵒᵖ = CBPVAssoc^op

  ModelCBPVValueLiftUE : ∀ {A B : hSet L}
    (f : Categoryᴰ.Hom[_][_,_] C {𝒱} {𝒱} (Category.id WalkingArrow) A B)
    (Bᴰ : Categoryᴰ.ob[_] Cᴰ (𝒱 , B))
    → EqPsh.CartesianLiftUE Cᴰ CBPVAssoc CBPVIdR {𝒱 , A} {𝒱 , B}
        (Category.id WalkingArrow , f) Bᴰ
  ModelCBPVValueLiftUE f Bᴰ .EqPsh.UEⱽ.v x = Bᴰ (f x)
  ModelCBPVValueLiftUE f Bᴰ .EqPsh.UEⱽ.e _ xᴰ = xᴰ
  ModelCBPVValueLiftUE f Bᴰ .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
    ((𝒱 , X) , Xᴰ , g) .fst h = h
  ModelCBPVValueLiftUE f Bᴰ .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
    ((𝒱 , X) , Xᴰ , g) .snd .fst _ = refl
  ModelCBPVValueLiftUE f Bᴰ .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
    ((𝒱 , X) , Xᴰ , g) .snd .snd _ = refl

  ModelCBPV-Uⱽ : hasUⱽ Cᴰ
  ModelCBPV-Uⱽ {A = A} {B = B} f Bᴰ =
    EqCartesianLift→CartesianLift CBPVAssoc Cᴰ Bᴰ (𝒱 , A) (_ , f)
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR ue)
    where
    carrier = ModelCBPVValueLiftUE {A = A} {B = B .fst} f (Bᴰ .fst)
    ue : EqPsh.CartesianLiftUE Cᴰ CBPVAssoc CBPVIdR {𝒱 , A} {𝒞 , B}
      (_ , f) Bᴰ
    ue .EqPsh.UEⱽ.v = carrier .EqPsh.UEⱽ.v
    ue .EqPsh.UEⱽ.e = carrier .EqPsh.UEⱽ.e
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝒱 , Z) , Zᴰ , g) =
      carrier .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝒱 , Z) , Zᴰ , g)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝒞 , Z) , Zᴰ , ())

  ModelCBPV-Fⱽ : hasFⱽ Cᴰ
  ModelCBPV-Fⱽ {A = A} {B = B} f Aᴰ =
    EqCartesianLift→CartesianLift CBPVAssocᵒᵖ (Cᴰ ^opᴰᴰ) Aᴰ (𝒞 , B) (_ , f)
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdRᵒᵖ ue)
    module ModelCBPV-F where
    ∫Aᴰ : hSet L
    ∫Aᴰ = (Σ[ a ∈ ⟨ A ⟩ ] ⟨ Aᴰ a ⟩) , isSetΣ (A .snd) (λ a → Aᴰ a .snd)

    Free∫ : Category.ob (MODEL T L)
    Free∫ = FreeModel ⟨ ∫Aᴰ ⟩

    h : MODEL T L [ Free∫ , B ]
    h = recFM ⟨ ∫Aᴰ ⟩ B (λ x → f (x .fst))

    Fᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) B
    Fᴰ = FiberModelᴰ h

    elem : ∀ a → ⟨ Aᴰ a ⟩ → ⟨ Fᴰ .fst (f a) ⟩
    elem a aᴰ = var (a , aᴰ) , refl

    module _ {Z : Category.ob (MODEL T L)}
      (Zᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) Z)
      (ψ : MODEL T L [ B , Z ]) where
      private
        module ZᴰR = hSetReasoning (Z .fst) (λ z → ⟨ Zᴰ .fst z ⟩)

        hψ*Zᴰ : Modelᴰ Free∫ L
        hψ*Zᴰ = _*_ {M = Free∫} {N = Z} (h ⋆H ψ) Zᴰ

      introF : (∀ a → ⟨ Aᴰ a ⟩ → ⟨ Zᴰ .fst (ψ .fst (f a)) ⟩)
        → Categoryᴰ.Hom[_][_,_] (MODELᴰ T L L) ψ Fᴰ Zᴰ
      introF γᴰ = fiberᴰ-intro h ψ Zᴰ
        (elimFreeModel ⟨ ∫Aᴰ ⟩ hψ*Zᴰ (λ x → γᴰ (x .fst) (x .snd)))

      introF-β : ∀ γᴰ a aᴰ → introF γᴰ .fst (f a) (elem a aᴰ) ≡ γᴰ a aᴰ
      introF-β γᴰ a aᴰ = ZᴰR.rectifyOut (ZᴰR.reind-filler⁻ refl)

      introF-η : ∀ χᴰ → introF (λ a aᴰ → χᴰ .fst (f a) (elem a aᴰ)) ≡ χᴰ
      introF-η χᴰ =
        cong (fiberᴰ-intro h ψ Zᴰ)
          (sym (elimFreeModel-uniq ⟨ ∫Aᴰ ⟩ hψ*Zᴰ (fiberᴰ-restrict h ψ Zᴰ χᴰ)))
        ∙ fiberᴰ-η h ψ Zᴰ χᴰ

    ue : EqPsh.CartesianLiftUE (Cᴰ ^opᴰᴰ) CBPVAssocᵒᵖ CBPVIdRᵒᵖ (_ , f) Aᴰ
    ue .EqPsh.UEⱽ.v = Fᴰ
    ue .EqPsh.UEⱽ.e = elem
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , Z) , Zᴰ , ψ) .fst γᴰ = introF Zᴰ (ψ .snd) γᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , Z) , Zᴰ , ψ) .snd .fst γᴰ =
        funExt λ a → funExt λ aᴰ → introF-β Zᴰ (ψ .snd) γᴰ a aᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , Z) , Zᴰ , ψ) .snd .snd χᴰ = introF-η Zᴰ (ψ .snd) χᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , Z) , Zᴰ , ()) .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , Z) , Zᴰ , ()) .snd .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , Z) , Zᴰ , ()) .snd .snd

    πⱽ≡elem : CartesianLiftNotation.πⱽ (Cᴰ ^opᴰᴰ)
        (EqCartesianLift→CartesianLift CBPVAssocᵒᵖ (Cᴰ ^opᴰᴰ) Aᴰ (𝒞 , B)
          (_ , f) (EqPsh.UEⱽ→Reprⱽ _ CBPVIdRᵒᵖ ue))
      ≡ elem
    πⱽ≡elem = EqCartesianLift→CartesianLift-πⱽ CBPVAssocᵒᵖ (Cᴰ ^opᴰᴰ) Aᴰ
      (𝒞 , B) (_ , f) (EqPsh.UEⱽ→Reprⱽ _ CBPVIdRᵒᵖ ue)

  ModelCBPVⱽ : MultCBPVCatⱽ (ModelCBPV T .fst) (ℓ-suc L) L
  ModelCBPVⱽ .fst = Cᴰ
  ModelCBPVⱽ .snd .fst = ModelCBPV-Uⱽ
  ModelCBPVⱽ .snd .snd = ModelCBPV-Fⱽ
