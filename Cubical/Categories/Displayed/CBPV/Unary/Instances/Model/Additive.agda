-- Additive structure for the Set/Model unary CBPV model.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Algebra.Theory.Base
  hiding (ℓ; ℓᴰ; ℓᴰᴰ; ℓ'; ℓᴰ'; ℓᴰᴰ'; ℓ''; ℓᴰ''; ℓO; ℓA; ℓE)

open import Cubical.Categories.Category
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; l to 𝒱; r to 𝒞)
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Instances.Algebra.DisplayedModel
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
open import Cubical.Categories.Displayed.CBPV.Unary.Additive
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Multiplicative

private
  variable
    ℓO ℓA ℓE ℓEA : Level

open Category
open UniversalElement

module _ (T : Theory ℓO ℓA ℓE ℓEA) where
  open Theory T

  private
    L = ModelLevel T
    C = ModelCBPVEq T .fst
    Cop = C ^opᴰ

    MODELOb→Model : Category.ob (MODEL T L) → Model L
    MODELOb→Model B .fst .fst = ⟨ B .fst ⟩
    MODELOb→Model B .fst .snd = B .snd .fst
    MODELOb→Model B .snd .fst = B .snd .snd
    MODELOb→Model B .snd .snd = B .fst .snd

    MODELᴰOb→Modelᴰ : ∀ {B : Category.ob (MODEL T L)}
      → Categoryᴰ.ob[_] (MODELᴰ T L L) B
      → Modelᴰ (MODELOb→Model B) L
    MODELᴰOb→Modelᴰ Bᴰ .fst .fst b = ⟨ Bᴰ .fst b ⟩
    MODELᴰOb→Modelᴰ Bᴰ .fst .snd = Bᴰ .snd .fst
    MODELᴰOb→Modelᴰ Bᴰ .snd .fst = Bᴰ .snd .snd
    MODELᴰOb→Modelᴰ Bᴰ .snd .snd b = Bᴰ .fst b .snd

    KIND-idR : EqPsh.EqIdR KIND
    KIND-idR _ = Eq.refl

    KIND^op-idR : EqPsh.EqIdR (KIND ^op)
    KIND^op-idR _ = Eq.refl

  ModelValueTerminalEqⱽ : EqTerminalⱽ C 𝒱
  ModelValueTerminalEqⱽ = EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = C} {P = KIND [-, 𝒱 ]}) KIND-idR
    ue .EqPsh.UEⱽ.v = Unit* , isSetUnit*
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .snd h =
      funExt λ _ → refl

  ModelValueProductEqⱽ : ∀ A₁ A₂ → EqBinProductⱽ C {k = 𝒱} A₁ A₂
  ModelValueProductEqⱽ A₁ A₂ = EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    ue : EqPsh.UEⱽ
      ((EqPsh._[-][-,_] C A₁) EqPsh.×ⱽPsh (EqPsh._[-][-,_] C A₂))
      KIND-idR
    ue .EqPsh.UEⱽ.v .fst = A₁ .fst × A₂ .fst
    ue .EqPsh.UEⱽ.v .snd = isSet× (A₁ .snd) (A₂ .snd)
    ue .EqPsh.UEⱽ.e = fst , snd
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .fst
      (p , q) x = p x , q x
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .snd _ = refl

  ModelValueInitialEqⱽ : EqInitialⱽ C 𝒱
  ModelValueInitialEqⱽ = EqPsh.UEⱽ→Reprⱽ _ KIND^op-idR ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = Cop} {P = (KIND ^op) [-, 𝒱 ]})
      KIND^op-idR
    ue .EqPsh.UEⱽ.v = ⊥* , isProp→isSet isProp⊥*
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .fst _ = λ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .fst _ = λ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .snd h =
      funExt λ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .snd .snd h =
      funExt λ ()

  ModelValueCoProductEqⱽ : ∀ A₁ A₂ →
    EqBinCoProductⱽ C {k = 𝒱} A₁ A₂
  ModelValueCoProductEqⱽ A₁ A₂ =
    EqPsh.UEⱽ→Reprⱽ _ KIND^op-idR ue
    where
    case-η : ∀ {X : Type L} (h : A₁ .fst ⊎ A₂ .fst → X) →
      Sum.rec (λ x → h (inl x)) (λ x → h (inr x)) ≡ h
    case-η h = funExt λ { (inl _) → refl ; (inr _) → refl }

    ue : EqPsh.UEⱽ
      ((EqPsh._[-][-,_] Cop A₁) EqPsh.×ⱽPsh
       (EqPsh._[-][-,_] Cop A₂))
      KIND^op-idR
    ue .EqPsh.UEⱽ.v .fst = A₁ .fst ⊎ A₂ .fst
    ue .EqPsh.UEⱽ.v .snd = isSet⊎ (A₁ .snd) (A₂ .snd)
    ue .EqPsh.UEⱽ.e = inl , inr
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .fst
      (p , q) = Sum.rec p q
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .fst
      (p , q) = Sum.rec p q
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .snd h =
      case-η h
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .snd .snd h =
      case-η h

  ModelComputationTerminalEqⱽ : EqTerminalⱽ C 𝒞
  ModelComputationTerminalEqⱽ = EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = C} {P = KIND [-, 𝒞 ]}) KIND-idR
    ue .EqPsh.UEⱽ.v = TerminalMODEL T .vertex
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .fst _ .fst _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .fst _ .snd
      _ _ _ _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .snd h =
      funExt λ _ → refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .snd .snd h =
      Σ≡Prop (λ _ → isPropΠ4 λ _ _ _ _ → isSetUnit* _ _)
        (funExt λ _ → refl)

  ModelComputationProductEqⱽ : ∀ B₁ B₂ →
    EqBinProductⱽ C {k = 𝒞} B₁ B₂
  ModelComputationProductEqⱽ B₁ B₂ =
    EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    ue : EqPsh.UEⱽ
      ((EqPsh._[-][-,_] C B₁) EqPsh.×ⱽPsh
       (EqPsh._[-][-,_] C B₂))
      KIND-idR
    ue .EqPsh.UEⱽ.v =
      BinProductsMODEL T (B₁ , B₂) .vertex
    ue .EqPsh.UEⱽ.e .fst .fst = fst
    ue .EqPsh.UEⱽ.e .fst .snd _ _ _ p = cong fst p
    ue .EqPsh.UEⱽ.e .snd .fst = snd
    ue .EqPsh.UEⱽ.e .snd .snd _ _ _ p = cong snd p
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .fst
      (p , q) x = p x , q x
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .fst
      (p , q) = ×intro p q
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒱 , A , f) .snd .snd _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝒞 , B , f) .snd .snd h =
      Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ →
          isSet× (B₁ .fst .snd) (B₂ .fst .snd) _ _)
        refl

  ModelAddCBPVEqWithFree : LeftAdjoint (MODELForget T)
    → AddCBPVCatEq (ℓ-suc L) L
  ModelAddCBPVEqWithFree Free .fst = ModelCBPVEqWithFree T Free
  ModelAddCBPVEqWithFree Free .snd .fst = ModelValueTerminalEqⱽ
  ModelAddCBPVEqWithFree Free .snd .snd .fst = ModelValueProductEqⱽ
  ModelAddCBPVEqWithFree Free .snd .snd .snd .fst = ModelValueInitialEqⱽ
  ModelAddCBPVEqWithFree Free .snd .snd .snd .snd .fst =
    ModelValueCoProductEqⱽ
  ModelAddCBPVEqWithFree Free .snd .snd .snd .snd .snd .fst =
    ModelComputationTerminalEqⱽ
  ModelAddCBPVEqWithFree Free .snd .snd .snd .snd .snd .snd =
    ModelComputationProductEqⱽ

  ModelAddCBPVWithFree : LeftAdjoint (MODELForget T)
    → AddCBPVCat (ℓ-suc L) L
  ModelAddCBPVWithFree Free = forgetAddEq (ModelAddCBPVEqWithFree Free)

  ModelAddCBPVEq : AddCBPVCatEq (ℓ-suc L) L
  ModelAddCBPVEq = ModelAddCBPVEqWithFree (MODELFree T)

  ModelAddCBPV : AddCBPVCat (ℓ-suc L) L
  ModelAddCBPV = ModelAddCBPVWithFree (MODELFree T)

  private
    Cᴰ = ModelCBPVᴰ T

    CBPVIdR : EqPsh.EqIdR (∫C C)
    CBPVIdR {x = 𝒱 , A} {y = 𝒱 , B} f = Eq.refl
    CBPVIdR {x = 𝒱 , A} {y = 𝒞 , B} f = Eq.refl
    CBPVIdR {x = 𝒞 , A} {y = 𝒱 , B} ()
    CBPVIdR {x = 𝒞 , A} {y = 𝒞 , B} f = Eq.refl

    CBPVAssoc : EqPsh.ReprEqAssoc (∫C C)
    CBPVAssoc (𝒱 , A)
      {c = 𝒱 , W} {c' = 𝒱 , X} {c'' = 𝒱 , Y}
      _ _ _ _ Eq.refl = Eq.refl
    CBPVAssoc (𝒞 , B)
      {c = 𝒱 , W} {c' = 𝒱 , X} {c'' = 𝒱 , Y}
      _ _ _ _ Eq.refl = Eq.refl
    CBPVAssoc (𝒞 , B)
      {c = 𝒱 , W} {c' = 𝒞 , X} {c'' = 𝒞 , Y}
      _ _ _ _ Eq.refl = Eq.refl
    CBPVAssoc (𝒞 , B)
      {c = 𝒞 , W} {c' = 𝒞 , X} {c'' = 𝒞 , Y}
      _ _ _ _ Eq.refl = Eq.refl
    CBPVAssoc x f g p f⋆g e = Eq.pathToEq
      (sym (D.⋆Assoc f g p) ∙ cong (λ fg → fg D.⋆ p) (Eq.eqToPath e))
      where module D = Category (∫C C)

    CBPVAssoc^op : EqPsh.ReprEqAssoc ((∫C C) ^op)
    CBPVAssoc^op (𝒱 , A)
      {c = 𝒱 , W} {c' = 𝒱 , X} {c'' = 𝒱 , Y}
      _ _ _ _ Eq.refl = Eq.refl
    CBPVAssoc^op (𝒱 , A)
      {c = 𝒞 , W} {c' = 𝒱 , X} {c'' = 𝒱 , Y}
      _ _ _ _ Eq.refl = Eq.refl
    CBPVAssoc^op x f g p f⋆g e = Eq.pathToEq
      (sym (D.⋆Assoc f g p) ∙ cong (λ fg → fg D.⋆ p) (Eq.eqToPath e))
      where module D = Category ((∫C C) ^op)

    CBPVIdR^op : EqPsh.EqIdR ((∫C C) ^op)
    CBPVIdR^op {x = 𝒱 , X} {y = 𝒱 , Y} f = Eq.refl
    CBPVIdR^op {x = 𝒞 , X} {y = 𝒱 , Y} f = Eq.refl
    CBPVIdR^op {x = 𝒱 , X} {y = 𝒞 , Y} ()
    CBPVIdR^op {x = 𝒞 , X} {y = 𝒞 , Y} f = Eq.refl

  ModelCBPVValueTerminalsⱽ : ValueTerminalsⱽ Cᴰ
  ModelCBPVValueTerminalsⱽ A =
    EqTerminalⱽ→Terminalⱽ CBPVAssoc Cᴰ
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR ue)
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = Cᴰ} {P = (∫C C) [-, (𝒱 , A) ]})
      CBPVIdR
    ue .EqPsh.UEⱽ.v _ = Unit* , isSetUnit*
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .fst _ _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , ()) .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , ()) .snd .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .snd _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , ()) .snd .snd

  ModelCBPVValueBinProductsⱽ : ValueBinProductsⱽ Cᴰ
  ModelCBPVValueBinProductsⱽ {A} A₁ᴰ A₂ᴰ =
    EqBinProductⱽ→BinProductⱽ CBPVAssoc Cᴰ
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR ue)
    where
    ue : EqPsh.UEⱽ
      ((Cᴰ EqPsh.[-][-, A₁ᴰ ]) EqPsh.×ⱽPsh
       (Cᴰ EqPsh.[-][-, A₂ᴰ ]))
      CBPVIdR
    ue .EqPsh.UEⱽ.v x =
      (A₁ᴰ x .fst × A₂ᴰ x .fst) , isSet× (A₁ᴰ x .snd) (A₂ᴰ x .snd)
    ue .EqPsh.UEⱽ.e = (λ _ → fst) , (λ _ → snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .fst (p , q) x xᴰ = p x xᴰ , q x xᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , ()) .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , ()) .snd .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .snd _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , ()) .snd .snd

  ModelCBPVValueInitialsⱽ : ValueInitialsⱽ Cᴰ
  ModelCBPVValueInitialsⱽ A =
    EqTerminalⱽ→Terminalⱽ CBPVAssoc^op (Cᴰ ^opᴰ)
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR^op ue)
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = Cᴰ ^opᴰ}
        {P = ((∫C C) ^op) [-, (𝒱 , A) ]})
      CBPVIdR^op
    ue .EqPsh.UEⱽ.v _ = ⊥* , isProp→isSet isProp⊥*
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .fst _ _ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .fst _ _ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .snd h = funExt₂ λ _ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .snd .snd h = funExt₂ λ _ ()

  ModelCBPVValueBinCoProductsⱽ : ValueBinCoProductsⱽ Cᴰ
  ModelCBPVValueBinCoProductsⱽ {A} A₁ᴰ A₂ᴰ =
    EqBinProductⱽ→BinProductⱽ CBPVAssoc^op (Cᴰ ^opᴰ)
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR^op ue)
    where
    case-η : ∀ {X : A .fst → Type L}
      (h : ∀ a → A₁ᴰ a .fst ⊎ A₂ᴰ a .fst → X a) →
      (λ a → Sum.rec (λ x → h a (inl x)) (λ x → h a (inr x))) ≡ h
    case-η h = funExt₂ λ _ → λ { (inl _) → refl ; (inr _) → refl }

    ue : EqPsh.UEⱽ
      (((Cᴰ ^opᴰ) EqPsh.[-][-, A₁ᴰ ]) EqPsh.×ⱽPsh
       ((Cᴰ ^opᴰ) EqPsh.[-][-, A₂ᴰ ]))
      CBPVIdR^op
    ue .EqPsh.UEⱽ.v a =
      (A₁ᴰ a .fst ⊎ A₂ᴰ a .fst) , isSet⊎ (A₁ᴰ a .snd) (A₂ᴰ a .snd)
    ue .EqPsh.UEⱽ.e = (λ _ → inl) , (λ _ → inr)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .fst (p , q) a = Sum.rec (p a) (q a)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .fst (p , q) a = Sum.rec (p a) (q a)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .snd h = case-η h
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .snd .snd h = case-η h

  ModelCBPVValueCartesianLifts : hasVerticalCartesianLiftsAt Cᴰ 𝒱
  ModelCBPVValueCartesianLifts {A} {B} f Bᴰ =
    EqCartesianLift→CartesianLift CBPVAssoc Cᴰ Bᴰ (𝒱 , A) (_ , f)
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR ue)
    where
    ue : EqPsh.CartesianLiftUE Cᴰ CBPVAssoc CBPVIdR (_ , f) Bᴰ
    ue .EqPsh.UEⱽ.v x = Bᴰ (f x)
    ue .EqPsh.UEⱽ.e _ xᴰ = xᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , g) .fst h = h
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , g) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , g) .snd .snd _ = refl

  ModelCBPVValueOpcartesianLifts :
    hasVerticalOpcartesianLiftsAt Cᴰ 𝒱
  ModelCBPVValueOpcartesianLifts {A} {B} f Aᴰ =
    EqCartesianLift→CartesianLift CBPVAssoc^op (Cᴰ ^opᴰ)
      Aᴰ (𝒱 , B) (_ , f) (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR^op ue)
    where
    ue : EqPsh.CartesianLiftUE (Cᴰ ^opᴰ)
      CBPVAssoc^op CBPVIdR^op (_ , f) Aᴰ
    ue .EqPsh.UEⱽ.v b .fst =
      Σ[ a ∈ A .fst ] (f a ≡ b) × Aᴰ a .fst
    ue .EqPsh.UEⱽ.v b .snd =
      isSetΣ (A .snd) λ a →
        isSet× (isProp→isSet (B .snd _ _)) (Aᴰ a .snd)
    ue .EqPsh.UEⱽ.e a aᴰ = a , refl , aᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , g) .fst h b (a , p , aᴰ) =
        subst (λ b' → Xᴰ (g .snd b') .fst) p (h a aᴰ)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , g) .fst h b (a , p , aᴰ) =
        subst (λ b' → Xᴰ .fst (g .snd b') .fst) p (h a aᴰ)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , g) .snd .fst h =
        funExt₂ λ _ _ → transportRefl _
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , g) .snd .fst h =
        funExt₂ λ _ _ → transportRefl _
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , g) .snd .snd h =
        funExt λ b → funExt λ { (a , p , aᴰ) →
          J (λ b' p' →
            subst (λ b'' → Xᴰ (g .snd b'') .fst) p'
              (h (f a) (a , refl , aᴰ)) ≡ h b' (a , p' , aᴰ))
            (transportRefl _) p }
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , g) .snd .snd h =
        funExt λ b → funExt λ { (a , p , aᴰ) →
          J (λ b' p' →
            subst (λ b'' → Xᴰ .fst (g .snd b'') .fst) p'
              (h (f a) (a , refl , aᴰ)) ≡ h b' (a , p' , aᴰ))
            (transportRefl _) p }

  ModelCBPVComputationTerminalsⱽ : ComputationTerminalsⱽ Cᴰ
  ModelCBPVComputationTerminalsⱽ B =
    EqTerminalⱽ→Terminalⱽ CBPVAssoc Cᴰ
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR ue)
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = Cᴰ} {P = (∫C C) [-, (𝒞 , B) ]})
      CBPVIdR
    ue .EqPsh.UEⱽ.v = TerminalsⱽMODELᴰ T B .fst
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .fst _ _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .fst _ .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .fst _ .snd _ _ _ _ _ _ _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .snd h = funExt₂ λ _ _ → refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .snd .snd h =
        MODELᴰHomo≡ T _ h (funExt₂ λ _ _ → refl)

  ModelCBPVComputationBinProductsⱽ : ComputationBinProductsⱽ Cᴰ
  ModelCBPVComputationBinProductsⱽ {B} B₁ᴰ B₂ᴰ =
    EqBinProductⱽ→BinProductⱽ CBPVAssoc Cᴰ
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR ue)
    where
    ue : EqPsh.UEⱽ
      ((Cᴰ EqPsh.[-][-, B₁ᴰ ]) EqPsh.×ⱽPsh
       (Cᴰ EqPsh.[-][-, B₂ᴰ ]))
      CBPVIdR
    ue .EqPsh.UEⱽ.v = BinProductsⱽMODELᴰ T B₁ᴰ B₂ᴰ .fst
    ue .EqPsh.UEⱽ.e .fst .fst _ = fst
    ue .EqPsh.UEⱽ.e .fst .snd _ _ _ _ _ _ p = cong fst p
    ue .EqPsh.UEⱽ.e .snd .fst _ = snd
    ue .EqPsh.UEⱽ.e .snd .snd _ _ _ _ _ _ p = cong snd p
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .fst (p , q) x xᴰ = p x xᴰ , q x xᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .fst (p , q) .fst x xᴰ =
        p .fst x xᴰ , q .fst x xᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .fst (p , q) .snd
      op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ i =
        p .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
          op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ i ,
        q .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
          op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ i
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , f) .snd .snd h = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , f) .snd .snd h = MODELᴰHomo≡ T _ h refl

  ModelCBPVComputationCartesianLifts :
    hasVerticalCartesianLiftsAt Cᴰ 𝒞
  ModelCBPVComputationCartesianLifts {A} {B} f Bᴰ =
    EqCartesianLift→CartesianLift CBPVAssoc Cᴰ Bᴰ (𝒞 , A) (_ , f)
      (EqPsh.UEⱽ→Reprⱽ _ CBPVIdR ue)
    where
    pullModelᴰ : Modelᴰ (MODELOb→Model A) L
    pullModelᴰ = Theory._*_ T f (MODELᴰOb→Modelᴰ Bᴰ)

    pullᴰ : Fibers.ob[_] Cᴰ (𝒞 , A)
    pullᴰ .fst a = Bᴰ .fst (f .fst a)
    pullᴰ .snd .fst = pullModelᴰ .fst .snd
    pullᴰ .snd .snd = pullModelᴰ .snd .fst

    ue : EqPsh.CartesianLiftUE Cᴰ CBPVAssoc CBPVIdR (_ , f) Bᴰ
    ue .EqPsh.UEⱽ.v = pullᴰ
    ue .EqPsh.UEⱽ.e .fst _ aᴰ = aᴰ
    ue .EqPsh.UEⱽ.e .snd
      op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
        op∘γᴰ≡op⟨γᴰ⟩
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , g) .fst h = h
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , g) .fst h = h
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , g) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , g) .snd .fst h = MODELᴰHomo≡ T _ h refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒱 , X) , Xᴰ , g) .snd .snd _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝒞 , X) , Xᴰ , g) .snd .snd h = MODELᴰHomo≡ T _ h refl

  ModelAddCBPVⱽWithFree : (Free : FreeMODELConstruction T) →
    AddCBPVCatⱽ (ModelAddCBPVWithFree (Free .fst) .fst .fst)
      (ℓ-suc L) L
  ModelAddCBPVⱽWithFree Free .fst = ModelCBPVⱽWithFree T Free
  ModelAddCBPVⱽWithFree Free .snd .fst = ModelCBPVValueTerminalsⱽ
  ModelAddCBPVⱽWithFree Free .snd .snd .fst =
    ModelCBPVValueBinProductsⱽ
  ModelAddCBPVⱽWithFree Free .snd .snd .snd .fst =
    ModelCBPVValueCartesianLifts
  ModelAddCBPVⱽWithFree Free .snd .snd .snd .snd .fst =
    ModelCBPVValueInitialsⱽ
  ModelAddCBPVⱽWithFree Free .snd .snd .snd .snd .snd .fst =
    ModelCBPVValueBinCoProductsⱽ
  ModelAddCBPVⱽWithFree Free .snd .snd .snd .snd .snd .snd .fst =
    ModelCBPVValueOpcartesianLifts
  ModelAddCBPVⱽWithFree Free .snd .snd .snd .snd .snd .snd .snd .fst =
    ModelCBPVComputationTerminalsⱽ
  ModelAddCBPVⱽWithFree Free .snd .snd .snd .snd .snd .snd .snd .snd .fst =
    ModelCBPVComputationBinProductsⱽ
  ModelAddCBPVⱽWithFree Free .snd .snd .snd .snd .snd .snd .snd .snd .snd =
    ModelCBPVComputationCartesianLifts

  ModelAddCBPVⱽ :
    AddCBPVCatⱽ (ModelAddCBPV .fst .fst) (ℓ-suc L) L
  ModelAddCBPVⱽ =
    ModelAddCBPVⱽWithFree (CanonicalFreeMODELConstruction T)
