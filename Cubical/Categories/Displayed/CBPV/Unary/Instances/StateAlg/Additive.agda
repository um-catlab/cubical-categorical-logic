-- Additive structure for the Set/StateAlg unary CBPV model.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Algebra.State
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; l to 𝓥; r to 𝓒)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Opposite
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
open import Cubical.Categories.Displayed.CBPV.Unary.Additive
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Base

private
  variable
    ℓ : Level

StateAlgTerminal : StateAlgebra ℓ
StateAlgTerminal .fst = Unit* , isSetUnit*
StateAlgTerminal .snd .StateAlg.rd _ _ = tt*
StateAlgTerminal .snd .StateAlg.wt _ _ = tt*
StateAlgTerminal .snd .StateAlg.wt-rd _ _ _ = refl
StateAlgTerminal .snd .StateAlg.rd-wt _ = refl
StateAlgTerminal .snd .StateAlg.wt-wt _ _ _ = refl

StateAlgProduct : StateAlgebra ℓ → StateAlgebra ℓ → StateAlgebra ℓ
StateAlgProduct B₁ B₂ .fst .fst = B₁ .fst .fst × B₂ .fst .fst
StateAlgProduct B₁ B₂ .fst .snd = isSet× (B₁ .fst .snd) (B₂ .fst .snd)
StateAlgProduct B₁ B₂ .snd .StateAlg.rd (x₁ , x₂) (y₁ , y₂) =
  B₁ .snd .StateAlg.rd x₁ y₁ , B₂ .snd .StateAlg.rd x₂ y₂
StateAlgProduct B₁ B₂ .snd .StateAlg.wt b (x₁ , x₂) =
  B₁ .snd .StateAlg.wt b x₁ , B₂ .snd .StateAlg.wt b x₂
StateAlgProduct B₁ B₂ .snd .StateAlg.wt-rd false xt xf i =
  B₁ .snd .StateAlg.wt-rd false (xt .fst) (xf .fst) i ,
  B₂ .snd .StateAlg.wt-rd false (xt .snd) (xf .snd) i
StateAlgProduct B₁ B₂ .snd .StateAlg.wt-rd true xt xf i =
  B₁ .snd .StateAlg.wt-rd true (xt .fst) (xf .fst) i ,
  B₂ .snd .StateAlg.wt-rd true (xt .snd) (xf .snd) i
StateAlgProduct B₁ B₂ .snd .StateAlg.rd-wt x i =
  B₁ .snd .StateAlg.rd-wt (x .fst) i ,
  B₂ .snd .StateAlg.rd-wt (x .snd) i
StateAlgProduct B₁ B₂ .snd .StateAlg.wt-wt b b' x i =
  B₁ .snd .StateAlg.wt-wt b b' (x .fst) i ,
  B₂ .snd .StateAlg.wt-wt b b' (x .snd) i

module _ (ℓ : Level) where
  private
    C = StateAlgCBPV {ℓ = ℓ} .fst
    Cop = C ^opᴰ
    KIND-idR : EqPsh.EqIdR KIND
    KIND-idR _ = Eq.refl
    KIND^op-idR : EqPsh.EqIdR (KIND ^op)
    KIND^op-idR _ = Eq.refl

  StateAlgValueTerminalEqⱽ : EqTerminalⱽ C 𝓥
  StateAlgValueTerminalEqⱽ = EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = C} {P = KIND [-, 𝓥 ]}) KIND-idR
    ue .EqPsh.UEⱽ.v = Unit* , isSetUnit*
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd h =
      funExt λ _ → refl

  StateAlgValueProductEqⱽ : ∀ A₁ A₂ → EqBinProductⱽ C {k = 𝓥} A₁ A₂
  StateAlgValueProductEqⱽ A₁ A₂ = EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    ue : EqPsh.UEⱽ
      ((EqPsh._[-][-,_] C A₁) EqPsh.×ⱽPsh (EqPsh._[-][-,_] C A₂))
      KIND-idR
    ue .EqPsh.UEⱽ.v .fst = A₁ .fst × A₂ .fst
    ue .EqPsh.UEⱽ.v .snd = isSet× (A₁ .snd) (A₂ .snd)
    ue .EqPsh.UEⱽ.e = fst , snd
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .fst
      (p , q) x = p x , q x
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd _ = refl

  StateAlgValueInitialEqⱽ : EqInitialⱽ C 𝓥
  StateAlgValueInitialEqⱽ = EqPsh.UEⱽ→Reprⱽ _ KIND^op-idR ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = Cop} {P = (KIND ^op) [-, 𝓥 ]})
      KIND^op-idR
    ue .EqPsh.UEⱽ.v = ⊥* , isProp→isSet isProp⊥*
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .fst _ = λ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .fst _ = λ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd h =
      funExt λ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .snd h =
      funExt λ ()

  StateAlgValueCoProductEqⱽ : ∀ A₁ A₂ →
    EqBinCoProductⱽ C {k = 𝓥} A₁ A₂
  StateAlgValueCoProductEqⱽ A₁ A₂ =
    EqPsh.UEⱽ→Reprⱽ _ KIND^op-idR ue
    where
    case-η : ∀ {X : Type ℓ} (h : A₁ .fst ⊎ A₂ .fst → X) →
      Sum.rec (h ∘ inl) (h ∘ inr) ≡ h
    case-η h = funExt λ { (inl _) → refl ; (inr _) → refl }

    ue : EqPsh.UEⱽ
      ((EqPsh._[-][-,_] Cop A₁) EqPsh.×ⱽPsh
       (EqPsh._[-][-,_] Cop A₂))
      KIND^op-idR
    ue .EqPsh.UEⱽ.v .fst = A₁ .fst ⊎ A₂ .fst
    ue .EqPsh.UEⱽ.v .snd = isSet⊎ (A₁ .snd) (A₂ .snd)
    ue .EqPsh.UEⱽ.e = inl , inr
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .fst
      (p , q) = Sum.rec p q
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .fst
      (p , q) = Sum.rec p q
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd h =
      case-η h
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .snd h =
      case-η h

  StateAlgComputationTerminalEqⱽ : EqTerminalⱽ C 𝓒
  StateAlgComputationTerminalEqⱽ = EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = C} {P = KIND [-, 𝓒 ]}) KIND-idR
    ue .EqPsh.UEⱽ.v = StateAlgTerminal
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .fst _ .fst _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .fst _ .snd
      .Homo.rd-hom _ _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .fst _ .snd
      .Homo.wt-hom _ _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd h =
      funExt λ _ → refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .snd h =
      StateAlgHom≡ _ h (funExt λ _ → refl)

  StateAlgComputationProductEqⱽ :
    ∀ B₁ B₂ → EqBinProductⱽ C {k = 𝓒} B₁ B₂
  StateAlgComputationProductEqⱽ B₁ B₂ =
    EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    pairC : ∀ {B : StateAlgebra ℓ} → StateAlgHom B B₁ → StateAlgHom B B₂ →
      StateAlgHom B (StateAlgProduct B₁ B₂)
    pairC p q .fst x = p .fst x , q .fst x
    pairC p q .snd .Homo.rd-hom xt xf i =
      p .snd .Homo.rd-hom xt xf i , q .snd .Homo.rd-hom xt xf i
    pairC p q .snd .Homo.wt-hom b x i =
      p .snd .Homo.wt-hom b x i , q .snd .Homo.wt-hom b x i

    ue : EqPsh.UEⱽ
      ((EqPsh._[-][-,_] C B₁) EqPsh.×ⱽPsh (EqPsh._[-][-,_] C B₂))
      KIND-idR
    ue .EqPsh.UEⱽ.v = StateAlgProduct B₁ B₂
    ue .EqPsh.UEⱽ.e .fst = fst , record
      { rd-hom = λ _ _ → refl ; wt-hom = λ _ _ → refl }
    ue .EqPsh.UEⱽ.e .snd = snd , record
      { rd-hom = λ _ _ → refl ; wt-hom = λ _ _ → refl }
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .fst
      (p , q) x = p x , q x
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .fst
      (p , q) = pairC p q
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .fst (p , q) =
      ΣPathP (StateAlgHom≡ _ p refl , StateAlgHom≡ _ q refl)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd _ =
      refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .snd h =
      StateAlgHom≡ _ h refl

  StateAlgAddCBPVEq : AddCBPVCatEq (ℓ-suc ℓ) ℓ
  StateAlgAddCBPVEq .fst = StateAlgCBPVEq
  StateAlgAddCBPVEq .snd .fst = StateAlgValueTerminalEqⱽ
  StateAlgAddCBPVEq .snd .snd .fst = StateAlgValueProductEqⱽ
  StateAlgAddCBPVEq .snd .snd .snd .fst = StateAlgValueInitialEqⱽ
  StateAlgAddCBPVEq .snd .snd .snd .snd .fst = StateAlgValueCoProductEqⱽ
  StateAlgAddCBPVEq .snd .snd .snd .snd .snd .fst =
    StateAlgComputationTerminalEqⱽ
  StateAlgAddCBPVEq .snd .snd .snd .snd .snd .snd =
    StateAlgComputationProductEqⱽ

  StateAlgAddCBPV : AddCBPVCat (ℓ-suc ℓ) ℓ
  StateAlgAddCBPV = forgetAddEq StateAlgAddCBPVEq
