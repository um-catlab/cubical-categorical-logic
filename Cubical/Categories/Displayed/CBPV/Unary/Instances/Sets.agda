-- Sets and set-indexed families as a unary CBPV model.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; l to 𝓥; r to 𝓒)
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Weaken
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Sets as EqSET
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.CBPV.Unary.Additive
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.FromU

open Category
open Functor
open Functorᴰ

private
  variable
    ℓ ℓ' : Level

SetCBPV : ∀ ℓ → CBPVCat (ℓ-suc ℓ) ℓ
SetCBPV ℓ = weaken KIND (SET ℓ)

SetCBPVEq : ∀ ℓ → MultCBPVCatEq (ℓ-suc ℓ) ℓ
SetCBPVEq ℓ =
  U→MultCBPVEq (Id {C = SET ℓ}) (IdLeftAdj (SET ℓ))

module _ (ℓ : Level) where
  private
    C = SetCBPVEq ℓ .fst
    Cop = C ^opᴰ
    KIND-idR : EqPsh.EqIdR KIND
    KIND-idR _ = Eq.refl
    KIND^op-idR : EqPsh.EqIdR (KIND ^op)
    KIND^op-idR _ = Eq.refl

  SetCBPVValueTerminalEqⱽ : EqTerminalⱽ C 𝓥
  SetCBPVValueTerminalEqⱽ = EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = C} {P = KIND [-, 𝓥 ]}) KIND-idR
    ue .EqPsh.UEⱽ.v = Unit* , isSetUnit*
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd h =
      funExt λ _ → refl

  SetCBPVValueProductEqⱽ : ∀ A₁ A₂ → EqBinProductⱽ C {k = 𝓥} A₁ A₂
  SetCBPVValueProductEqⱽ A₁ A₂ = EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
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

  SetCBPVValueInitialEqⱽ : EqInitialⱽ C 𝓥
  SetCBPVValueInitialEqⱽ = EqPsh.UEⱽ→Reprⱽ _ KIND^op-idR ue
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

  SetCBPVValueCoProductEqⱽ : ∀ A₁ A₂ →
    EqBinCoProductⱽ C {k = 𝓥} A₁ A₂
  SetCBPVValueCoProductEqⱽ A₁ A₂ =
    EqPsh.UEⱽ→Reprⱽ _ KIND^op-idR ue
    where
    case-η : ∀ {X : Type ℓ} (h : A₁ .fst ⊎ A₂ .fst → X) →
      Sum.rec (λ x → h (inl x)) (λ x → h (inr x)) ≡ h
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

  SetCBPVComputationTerminalEqⱽ : EqTerminalⱽ C 𝓒
  SetCBPVComputationTerminalEqⱽ = EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = C} {P = KIND [-, 𝓒 ]}) KIND-idR
    ue .EqPsh.UEⱽ.v = Unit* , isSetUnit*
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd h =
      funExt λ _ → refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .snd h =
      funExt λ _ → refl

  SetCBPVComputationProductEqⱽ : ∀ B₁ B₂ →
    EqBinProductⱽ C {k = 𝓒} B₁ B₂
  SetCBPVComputationProductEqⱽ B₁ B₂ =
    EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    ue : EqPsh.UEⱽ
      ((EqPsh._[-][-,_] C B₁) EqPsh.×ⱽPsh (EqPsh._[-][-,_] C B₂))
      KIND-idR
    ue .EqPsh.UEⱽ.v .fst = B₁ .fst × B₂ .fst
    ue .EqPsh.UEⱽ.v .snd = isSet× (B₁ .snd) (B₂ .snd)
    ue .EqPsh.UEⱽ.e = fst , snd
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .fst
      (p , q) x = p x , q x
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .fst
      (p , q) x = p x , q x
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .snd _ = refl

  SetAddCBPVEq : AddCBPVCatEq (ℓ-suc ℓ) ℓ
  SetAddCBPVEq .fst = SetCBPVEq ℓ
  SetAddCBPVEq .snd .fst = SetCBPVValueTerminalEqⱽ
  SetAddCBPVEq .snd .snd .fst = SetCBPVValueProductEqⱽ
  SetAddCBPVEq .snd .snd .snd .fst = SetCBPVValueInitialEqⱽ
  SetAddCBPVEq .snd .snd .snd .snd .fst = SetCBPVValueCoProductEqⱽ
  SetAddCBPVEq .snd .snd .snd .snd .snd .fst =
    SetCBPVComputationTerminalEqⱽ
  SetAddCBPVEq .snd .snd .snd .snd .snd .snd =
    SetCBPVComputationProductEqⱽ

  SetAddCBPV : AddCBPVCat (ℓ-suc ℓ) ℓ
  SetAddCBPV = forgetAddEq SetAddCBPVEq

SetCBPVᴰ : ∀ ℓ → CBPVCatᴰ (SetCBPV ℓ) (ℓ-suc ℓ) ℓ
SetCBPVᴰ ℓ = reindex (SETᴰ ℓ ℓ) (weakenΠ KIND (SET ℓ))

module _ (C : CBPVCat ℓ ℓ') where
  private
    module C = Categoryᴰ C

  points : C.ob[ 𝓥 ] → Functorⱽ C (SetCBPV ℓ')
  points A .F-obᴰ X = C.Hom[ _ ][ A , X ] , C.isSetHomᴰ
  points A .F-homᴰ f g = g C.⋆ᴰ f
  points A .F-idᴰ i g = C.⋆IdRᴰ g i
  points A .F-seqᴰ f g i h = C.⋆Assocᴰ h f g (~ i)

private
  SetCBPVΠ^op : ∀ ℓ → Functor (∫C (SetCBPV ℓ ^opᴰ)) (SET ℓ ^op)
  SetCBPVΠ^op ℓ .F-ob = snd
  SetCBPVΠ^op ℓ .F-hom = snd
  SetCBPVΠ^op ℓ .F-id = refl
  SetCBPVΠ^op ℓ .F-seq _ _ = refl

  SetCBPVΠTotal^op : ∀ ℓ → Functor ((∫C (SetCBPV ℓ)) ^op) (SET ℓ ^op)
  SetCBPVΠTotal^op ℓ .F-ob = snd
  SetCBPVΠTotal^op ℓ .F-hom = snd
  SetCBPVΠTotal^op ℓ .F-id = refl
  SetCBPVΠTotal^op ℓ .F-seq _ _ = refl

  SET-fib : ∀ ℓ → isFibration (SETᴰ ℓ ℓ)
  SET-fib ℓ =
    EqFibration→Fibration EqSET.SetAssoc (SETᴰ ℓ ℓ) EqSET.SetᴰFibration

  SET-opfib : ∀ ℓ → isFibration ((SETᴰ ℓ ℓ) ^opᴰ)
  SET-opfib ℓ =
    EqFibration→Fibration EqSET.SetAssoc^op ((SETᴰ ℓ ℓ) ^opᴰ)
      EqSET.SetᴰFibration^op

SetCBPV-Uⱽ : ∀ ℓ → hasUⱽ (SetCBPVᴰ ℓ)
SetCBPV-Uⱽ ℓ f Bᴰ =
  reindexCartesianLift (SETᴰ ℓ ℓ) (weakenΠ KIND (SET ℓ)) (_ , f) Bᴰ
    (SET-fib ℓ Bᴰ _ f)

SetCBPV-Fⱽ : ∀ ℓ → hasFⱽ (SetCBPVᴰ ℓ)
SetCBPV-Fⱽ ℓ {A = A} {B = B} f Aᴰ =
  f*Aᴰ .fst ,
  pshiso
    (pshhom
      (λ x → f*Aᴰ .snd .PshIso.trans .PshHom.N-ob x)
      (λ c c' g p → f*Aᴰ .snd .PshIso.trans .PshHom.N-hom c c' g p))
    (f*Aᴰ .snd .PshIso.nIso)
  where
  f*Aᴰ : CartesianLift
    (reindex ((SETᴰ ℓ ℓ) ^opᴰ) (SetCBPVΠ^op ℓ))
    {x = 𝓒 , B} {y = 𝓥 , A} (_ , f) Aᴰ
  f*Aᴰ =
    reindexCartesianLift ((SETᴰ ℓ ℓ) ^opᴰ)
      (SetCBPVΠ^op ℓ) (_ , f) Aᴰ
      (SET-opfib ℓ Aᴰ _ f)

SetCBPVⱽ : ∀ ℓ → MultCBPVCatⱽ (SetCBPV ℓ) (ℓ-suc ℓ) ℓ
SetCBPVⱽ ℓ .fst = SetCBPVᴰ ℓ
SetCBPVⱽ ℓ .snd .fst = SetCBPV-Uⱽ ℓ
SetCBPVⱽ ℓ .snd .snd = SetCBPV-Fⱽ ℓ

private
  SETᴰCartesianⱽ : ∀ ℓ → CartesianCategoryⱽ (SET ℓ) (ℓ-suc ℓ) ℓ
  SETᴰCartesianⱽ ℓ =
    EqCCⱽ→CCⱽ EqSET.SetAssoc (SETᴰ ℓ ℓ) EqSET.isCartesianⱽSETᴰ

  SETᴰCartesianⱽ^op : ∀ ℓ → CartesianCategoryⱽ (SET ℓ ^op) (ℓ-suc ℓ) ℓ
  SETᴰCartesianⱽ^op ℓ =
    EqCCⱽ→CCⱽ EqSET.SetAssoc^op ((SETᴰ ℓ ℓ) ^opᴰ)
      EqSET.isCartesianⱽSETᴰ^op

  SetCBPVCartesianⱽ : ∀ ℓ → CartesianCategoryⱽ
    (∫C (SetCBPV ℓ)) (ℓ-suc ℓ) ℓ
  SetCBPVCartesianⱽ ℓ =
    CartesianCategoryⱽReindex (SETᴰCartesianⱽ ℓ) (weakenΠ KIND (SET ℓ))

  SetCBPVCartesianⱽ^op : ∀ ℓ → CartesianCategoryⱽ
    ((∫C (SetCBPV ℓ)) ^op) (ℓ-suc ℓ) ℓ
  SetCBPVCartesianⱽ^op ℓ =
    CartesianCategoryⱽReindex (SETᴰCartesianⱽ^op ℓ) (SetCBPVΠTotal^op ℓ)

module _ (ℓ : Level) where
  private
    module Cart = CartesianCategoryⱽ (SetCBPVCartesianⱽ ℓ)
    module OpCart = CartesianCategoryⱽ (SetCBPVCartesianⱽ^op ℓ)

  SetCBPV-Initialsⱽ : ValueInitialsⱽ (SetCBPVᴰ ℓ)
  SetCBPV-Initialsⱽ A =
    init' .fst ,
    pshiso
      (pshhom
        (λ x → init' .snd .PshIso.trans .PshHom.N-ob x)
        (λ _ _ _ _ → refl))
      (init' .snd .PshIso.nIso)
    where
    init' = OpCart.termⱽ (𝓥 , A)

  SetCBPV-BinCoProductsⱽ : ValueBinCoProductsⱽ (SetCBPVᴰ ℓ)
  SetCBPV-BinCoProductsⱽ A₁ᴰ A₂ᴰ =
    bcp' .fst ,
    pshiso
      (pshhom
        (λ x → bcp' .snd .PshIso.trans .PshHom.N-ob x)
        (λ x y f p → bcp' .snd .PshIso.trans .PshHom.N-hom x y f p))
      (bcp' .snd .PshIso.nIso)
    where
    bcp' = OpCart.bpⱽ A₁ᴰ A₂ᴰ

  SetCBPV-OpcartesianLifts :
    hasVerticalOpcartesianLiftsAt (SetCBPVᴰ ℓ) 𝓥
  SetCBPV-OpcartesianLifts f Aᴰ =
    lift' .fst ,
    pshiso
      (pshhom
        (λ x → lift' .snd .PshIso.trans .PshHom.N-ob x)
        (λ x y g p → lift' .snd .PshIso.trans .PshHom.N-hom x y g p))
      (lift' .snd .PshIso.nIso)
    where
    lift' = OpCart.cartesianLifts Aᴰ _ (_ , f)

  SetAddCBPVⱽ : AddCBPVCatⱽ (SetCBPV ℓ) (ℓ-suc ℓ) ℓ
  SetAddCBPVⱽ .fst = SetCBPVⱽ ℓ
  SetAddCBPVⱽ .snd .fst A = Cart.termⱽ (𝓥 , A)
  SetAddCBPVⱽ .snd .snd .fst = Cart.bpⱽ
  SetAddCBPVⱽ .snd .snd .snd .fst f Bᴰ =
    Cart.cartesianLifts Bᴰ _ (_ , f)
  SetAddCBPVⱽ .snd .snd .snd .snd .fst = SetCBPV-Initialsⱽ
  SetAddCBPVⱽ .snd .snd .snd .snd .snd .fst = SetCBPV-BinCoProductsⱽ
  SetAddCBPVⱽ .snd .snd .snd .snd .snd .snd .fst = SetCBPV-OpcartesianLifts
  SetAddCBPVⱽ .snd .snd .snd .snd .snd .snd .snd .fst B =
    Cart.termⱽ (𝓒 , B)
  SetAddCBPVⱽ .snd .snd .snd .snd .snd .snd .snd .snd .fst = Cart.bpⱽ
  SetAddCBPVⱽ .snd .snd .snd .snd .snd .snd .snd .snd .snd f Bᴰ =
    Cart.cartesianLifts Bᴰ _ (_ , f)
