-- Additive structure for the Set/StateAlg unary CBPV model.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Bool
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Algebra.State
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; l to 𝓥; r to 𝓒)
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Sets as EqSET
open import Cubical.Categories.Displayed.CBPV.Unary.Additive
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Vertical

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

private
  StateAlgIdR : ∀ ℓ → EqPsh.EqIdR (STATEALG ℓ)
  StateAlgIdR ℓ _ = Eq.refl

  StateAlgAssoc : ∀ ℓ → EqPsh.ReprEqAssoc (STATEALG ℓ)
  StateAlgAssoc ℓ _ _ _ _ _ Eq.refl = Eq.refl

  StateAlgᴰTerminalsEqⱽ : ∀ ℓ → EqPsh.Terminalsⱽ (STATEALGᴰ ℓ ℓ)
  StateAlgᴰTerminalsEqⱽ ℓ B =
    EqPsh.UEⱽ→Reprⱽ _ (StateAlgIdR ℓ) ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh
        {Cᴰ = STATEALGᴰ ℓ ℓ} {P = (STATEALG ℓ) [-, B ]})
      (StateAlgIdR ℓ)
    ue .EqPsh.UEⱽ.v .fst x = Unit* , isSetUnit*
    ue .EqPsh.UEⱽ.v .snd = Unitⱽ (B .snd) ℓ
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Z , Zᴰ , f) .fst _ .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Z , Zᴰ , f) .fst _ .snd = !ⱽ (f .snd) (Zᴰ .snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Z , Zᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Z , Zᴰ , f) .snd .snd h =
        ∫Homoᴰ≡ _ h (λ _ → isSetUnit*) (funExt₂ λ _ _ → refl)

  StateAlgᴰBinProductsEqⱽ : ∀ ℓ → EqPsh.BinProductsⱽ (STATEALGᴰ ℓ ℓ)
  StateAlgᴰBinProductsEqⱽ ℓ {x = B} B₁ᴰ B₂ᴰ =
    EqPsh.UEⱽ→Reprⱽ _ (StateAlgIdR ℓ) ue
    where
    ue : EqPsh.UEⱽ
      (((STATEALGᴰ ℓ ℓ EqPsh.[-][-, B₁ᴰ ]) EqPsh.×ⱽPsh
        (STATEALGᴰ ℓ ℓ EqPsh.[-][-, B₂ᴰ ])))
      (StateAlgIdR ℓ)
    ue .EqPsh.UEⱽ.v .fst x .fst =
      B₁ᴰ .fst x .fst × B₂ᴰ .fst x .fst
    ue .EqPsh.UEⱽ.v .fst x .snd =
      isSet× (B₁ᴰ .fst x .snd) (B₂ᴰ .fst x .snd)
    ue .EqPsh.UEⱽ.v .snd = Prodⱽ (B₁ᴰ .snd) (B₂ᴰ .snd)
    ue .EqPsh.UEⱽ.e .fst .fst _ = fst
    ue .EqPsh.UEⱽ.e .fst .snd = π₁ⱽ (B₁ᴰ .snd) (B₂ᴰ .snd)
    ue .EqPsh.UEⱽ.e .snd .fst _ = snd
    ue .EqPsh.UEⱽ.e .snd .snd = π₂ⱽ (B₁ᴰ .snd) (B₂ᴰ .snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Z , Zᴰ , f , ϕ) .fst (p , q) .fst z zᴰ =
        p .fst z zᴰ , q .fst z zᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Z , Zᴰ , f , ϕ) .fst (p , q) .snd =
        ×ⱽintroⱽ (B₁ᴰ .snd) (B₂ᴰ .snd) ϕ (p .snd) (q .snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Z , Zᴰ , f , ϕ) .snd .fst (p , q) = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Z , Zᴰ , f , ϕ) .snd .snd h =
        ∫Homoᴰ≡ _ h
          (λ x → isSet× (B₁ᴰ .fst x .snd) (B₂ᴰ .fst x .snd)) refl

  StateAlgᴰFibrationEq : ∀ ℓ →
    EqPsh.Fibration (STATEALGᴰ ℓ ℓ) (StateAlgAssoc ℓ)
  StateAlgᴰFibrationEq ℓ {x = Z} {y = B'} f Bᴰ' =
    EqPsh.UEⱽ→Reprⱽ _ (StateAlgIdR ℓ) ue
    where
    pullᴰ : Fibers.ob[_] (STATEALGᴰ ℓ ℓ) Z
    pullᴰ .fst z = Bᴰ' .fst (f .fst z)
    pullᴰ .snd = pull (f .snd) (Bᴰ' .snd) (B' .fst .snd)

    ue : EqPsh.CartesianLiftUE (STATEALGᴰ ℓ ℓ)
      (StateAlgAssoc ℓ) (StateAlgIdR ℓ) f Bᴰ'
    ue .EqPsh.UEⱽ.v = pullᴰ
    ue .EqPsh.UEⱽ.e .fst _ zᴰ = zᴰ
    ue .EqPsh.UEⱽ.e .snd =
      π-pull (f .snd) (Bᴰ' .snd) (B' .fst .snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Y , Yᴰ , g) .fst h .fst = h .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Y , Yᴰ , g) .fst h .snd =
        pull-intro (f .snd) (Bᴰ' .snd) (B' .fst .snd) (g .snd) (h .snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Y , Yᴰ , g) .snd .fst h =
        ∫Homoᴰ≡ _ h (λ x → Bᴰ' .fst x .snd) refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      (Y , Yᴰ , g) .snd .snd h =
        ∫Homoᴰ≡ _ h (λ y → Bᴰ' .fst (f .fst y) .snd) refl

  StateAlgᴰTerminalsⱽ : ∀ ℓ → Terminalsⱽ (STATEALGᴰ ℓ ℓ)
  StateAlgᴰTerminalsⱽ ℓ =
    EqTerminalsⱽ→Terminalsⱽ (StateAlgAssoc ℓ) (STATEALGᴰ ℓ ℓ)
      (StateAlgᴰTerminalsEqⱽ ℓ)

  StateAlgᴰBinProductsⱽ : ∀ ℓ → BinProductsⱽ (STATEALGᴰ ℓ ℓ)
  StateAlgᴰBinProductsⱽ ℓ =
    EqBinProductsⱽ→BinProductsⱽ (StateAlgAssoc ℓ) (STATEALGᴰ ℓ ℓ)
      (StateAlgᴰBinProductsEqⱽ ℓ)

  StateAlgᴰFibration : ∀ ℓ → isFibration (STATEALGᴰ ℓ ℓ)
  StateAlgᴰFibration ℓ =
    EqFibration→Fibration (StateAlgAssoc ℓ) (STATEALGᴰ ℓ ℓ)
      (StateAlgᴰFibrationEq ℓ)

  StateAlgCBPVIdR : ∀ ℓ → EqPsh.EqIdR (∫C (StateAlgCBPV {ℓ = ℓ} .fst))
  StateAlgCBPVIdR ℓ {x = 𝓥 , A} {y = 𝓥 , B} f = Eq.refl
  StateAlgCBPVIdR ℓ {x = 𝓥 , A} {y = 𝓒 , B} f =
    Eq.refl
  StateAlgCBPVIdR ℓ {x = 𝓒 , A} {y = 𝓥 , B} ()
  StateAlgCBPVIdR ℓ {x = 𝓒 , A} {y = 𝓒 , B} f =
    Eq.refl

  StateAlgCBPVAssoc : ∀ ℓ →
    EqPsh.ReprEqAssoc (∫C (StateAlgCBPV {ℓ = ℓ} .fst))
  StateAlgCBPVAssoc ℓ (𝓥 , A)
    {c = 𝓥 , W} {c' = 𝓥 , X} {c'' = 𝓥 , Y}
    _ _ _ _ Eq.refl = Eq.refl
  StateAlgCBPVAssoc ℓ (𝓒 , B)
    {c = 𝓥 , W} {c' = 𝓥 , X} {c'' = 𝓥 , Y}
    _ _ _ _ Eq.refl = Eq.refl
  StateAlgCBPVAssoc ℓ (𝓒 , B)
    {c = 𝓥 , W} {c' = 𝓒 , X} {c'' = 𝓒 , Y}
    _ _ _ _ Eq.refl = Eq.refl
  StateAlgCBPVAssoc ℓ (𝓒 , B)
    {c = 𝓒 , W} {c' = 𝓒 , X} {c'' = 𝓒 , Y}
    _ _ _ _ Eq.refl = Eq.refl
  StateAlgCBPVAssoc ℓ _ f g p f⋆g e = Eq.pathToEq
    (sym (TC.⋆Assoc f g p)
    ∙ cong (λ fg → fg TC.⋆ p) (Eq.eqToPath e))
    where module TC = Category (∫C (StateAlgCBPV {ℓ = ℓ} .fst))

  StateAlgCBPVValueTerminalsEqⱽ : ∀ ℓ A →
    EqPsh.Reprⱽ
      (EqPsh.UnitⱽPsh
        {Cᴰ = StateAlgCBPVᴰ ℓ ℓ}
        {P = (∫C (StateAlgCBPV {ℓ = ℓ} .fst)) [-, (𝓥 , A) ]})
  StateAlgCBPVValueTerminalsEqⱽ ℓ A =
    EqPsh.UEⱽ→Reprⱽ _ (StateAlgCBPVIdR ℓ) ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh
        {Cᴰ = StateAlgCBPVᴰ ℓ ℓ}
        {P = (∫C (StateAlgCBPV {ℓ = ℓ} .fst)) [-, (𝓥 , A) ]})
      (StateAlgCBPVIdR ℓ)
    ue .EqPsh.UEⱽ.v _ = Unit* , isSetUnit*
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , f) .fst _ _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , ()) .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , ()) .snd .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , f) .snd .snd _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , ()) .snd .snd

  StateAlgCBPVValueBinProductsEqⱽ : ∀ ℓ
    {A : Fibers.ob[_] (StateAlgCBPV {ℓ = ℓ} .fst) 𝓥}
    (A₁ᴰ A₂ᴰ : Fibers.ob[_] (StateAlgCBPVᴰ ℓ ℓ) (𝓥 , A)) →
    EqPsh.Reprⱽ
      ((EqPsh._[-][-,_] {x = (𝓥 , A)} (StateAlgCBPVᴰ ℓ ℓ) A₁ᴰ)
        EqPsh.×ⱽPsh
       (EqPsh._[-][-,_] {x = (𝓥 , A)} (StateAlgCBPVᴰ ℓ ℓ) A₂ᴰ))
  StateAlgCBPVValueBinProductsEqⱽ ℓ {A} A₁ᴰ A₂ᴰ =
    EqPsh.UEⱽ→Reprⱽ _ (StateAlgCBPVIdR ℓ) ue
    where
    ue : EqPsh.UEⱽ
      ((EqPsh._[-][-,_] {x = (𝓥 , A)} (StateAlgCBPVᴰ ℓ ℓ) A₁ᴰ)
        EqPsh.×ⱽPsh
       (EqPsh._[-][-,_] {x = (𝓥 , A)} (StateAlgCBPVᴰ ℓ ℓ) A₂ᴰ))
      (StateAlgCBPVIdR ℓ)
    ue .EqPsh.UEⱽ.v x =
      (A₁ᴰ x .fst × A₂ᴰ x .fst) , isSet× (A₁ᴰ x .snd) (A₂ᴰ x .snd)
    ue .EqPsh.UEⱽ.e = (λ _ → fst) , (λ _ → snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , f) .fst (p , q) x xᴰ = p x xᴰ , q x xᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , ()) .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , ()) .snd .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , f) .snd .snd _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , ()) .snd .snd

  StateAlgᴰCartesianⱽ : ∀ ℓ →
    CartesianCategoryⱽ (STATEALG ℓ) (ℓ-suc ℓ) ℓ
  StateAlgᴰCartesianⱽ ℓ .CartesianCategoryⱽ.Cᴰ = STATEALGᴰ ℓ ℓ
  StateAlgᴰCartesianⱽ ℓ .CartesianCategoryⱽ.termⱽ =
    StateAlgᴰTerminalsⱽ ℓ
  StateAlgᴰCartesianⱽ ℓ .CartesianCategoryⱽ.bpⱽ =
    StateAlgᴰBinProductsⱽ ℓ
  StateAlgᴰCartesianⱽ ℓ .CartesianCategoryⱽ.cartesianLifts =
    StateAlgᴰFibration ℓ

  StateAlgCBPVValueTerminalsⱽ :
    ∀ ℓ → ValueTerminalsⱽ (StateAlgCBPVᴰ ℓ ℓ)
  StateAlgCBPVValueTerminalsⱽ ℓ A =
    EqTerminalⱽ→Terminalⱽ (StateAlgCBPVAssoc ℓ) (StateAlgCBPVᴰ ℓ ℓ)
      (StateAlgCBPVValueTerminalsEqⱽ ℓ A)

  StateAlgCBPVValueBinProductsⱽ :
    ∀ ℓ → ValueBinProductsⱽ (StateAlgCBPVᴰ ℓ ℓ)
  StateAlgCBPVValueBinProductsⱽ ℓ {A} A₁ᴰ A₂ᴰ =
    EqBinProductⱽ→BinProductⱽ
      (StateAlgCBPVAssoc ℓ) (StateAlgCBPVᴰ ℓ ℓ)
      (StateAlgCBPVValueBinProductsEqⱽ ℓ A₁ᴰ A₂ᴰ)

  StateAlgCBPVAssoc^op : ∀ ℓ →
    EqPsh.ReprEqAssoc ((∫C (StateAlgCBPV {ℓ = ℓ} .fst)) ^op)
  StateAlgCBPVAssoc^op ℓ (𝓥 , A)
    {c = 𝓥 , W} {c' = 𝓥 , X} {c'' = 𝓥 , Y}
    _ _ _ _ Eq.refl = Eq.refl
  StateAlgCBPVAssoc^op ℓ (𝓥 , A)
    {c = 𝓒 , W} {c' = 𝓥 , X} {c'' = 𝓥 , Y}
    _ _ _ _ Eq.refl = Eq.refl
  StateAlgCBPVAssoc^op ℓ x f g p f⋆g e = Eq.pathToEq
    (sym (C.⋆Assoc f g p) ∙ cong (λ fg → fg C.⋆ p) (Eq.eqToPath e))
    where module C = Category ((∫C (StateAlgCBPV {ℓ = ℓ} .fst)) ^op)

  StateAlgCBPVValueInitialsEqⱽ : ∀ ℓ →
    ValueInitialsⱽ (StateAlgCBPVᴰ ℓ ℓ)
  StateAlgCBPVValueInitialsEqⱽ ℓ A =
    EqTerminalⱽ→Terminalⱽ (StateAlgCBPVAssoc^op ℓ)
      ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰ) (EqPsh.UEⱽ→Reprⱽ _ idR ue)
    where
    idR : EqPsh.EqIdR ((∫C (StateAlgCBPV {ℓ = ℓ} .fst)) ^op)
    idR {x = 𝓥 , X} {y = 𝓥 , Y} f = Eq.refl
    idR {x = 𝓒 , X} {y = 𝓥 , Y} f = Eq.refl
    idR {x = 𝓥 , X} {y = 𝓒 , Y} ()
    idR {x = 𝓒 , X} {y = 𝓒 , Y} f = Eq.refl
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = (StateAlgCBPVᴰ ℓ ℓ) ^opᴰ}
        {P = ((∫C (StateAlgCBPV {ℓ = ℓ} .fst)) ^op) [-, (𝓥 , A) ]}) idR
    ue .EqPsh.UEⱽ.v _ = ⊥* , isProp→isSet isProp⊥*
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .fst _ _ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .fst _ _ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .snd .snd h =
      funExt₂ λ _ ()
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .snd .snd h =
      funExt₂ λ _ ()

  StateAlgCBPVValueBinCoProductsEqⱽ : ∀ ℓ →
    ValueBinCoProductsⱽ (StateAlgCBPVᴰ ℓ ℓ)
  StateAlgCBPVValueBinCoProductsEqⱽ ℓ {A} A₁ᴰ A₂ᴰ =
    EqBinProductⱽ→BinProductⱽ (StateAlgCBPVAssoc^op ℓ)
      ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰ) (EqPsh.UEⱽ→Reprⱽ _ idR ue)
    where
    idR : EqPsh.EqIdR ((∫C (StateAlgCBPV {ℓ = ℓ} .fst)) ^op)
    idR {x = 𝓥 , X} {y = 𝓥 , Y} f = Eq.refl
    idR {x = 𝓒 , X} {y = 𝓥 , Y} f = Eq.refl
    idR {x = 𝓥 , X} {y = 𝓒 , Y} ()
    idR {x = 𝓒 , X} {y = 𝓒 , Y} f = Eq.refl
    case-η : ∀ {X : A .fst → Type ℓ}
      (h : ∀ a → (A₁ᴰ a .fst ⊎ A₂ᴰ a .fst) → X a) →
      (λ a → Sum.rec (h a ∘ inl) (h a ∘ inr)) ≡ h
    case-η h = funExt₂ λ _ → λ { (inl _) → refl ; (inr _) → refl }
    ue : EqPsh.UEⱽ
      (((StateAlgCBPVᴰ ℓ ℓ ^opᴰ) EqPsh.[-][-, A₁ᴰ ]) EqPsh.×ⱽPsh
       ((StateAlgCBPVᴰ ℓ ℓ ^opᴰ) EqPsh.[-][-, A₂ᴰ ])) idR
    ue .EqPsh.UEⱽ.v a =
      (A₁ᴰ a .fst ⊎ A₂ᴰ a .fst) , isSet⊎ (A₁ᴰ a .snd) (A₂ᴰ a .snd)
    ue .EqPsh.UEⱽ.e = (λ _ → inl) , (λ _ → inr)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .fst (p , q) a =
      Sum.rec (p a) (q a)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .fst (p , q) a =
      Sum.rec (p a) (q a)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .snd .snd h = case-η h
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .snd .snd h = case-η h

  StateAlgCBPVComputationTerminalsⱽ : ∀ ℓ →
    ComputationTerminalsⱽ (StateAlgCBPVᴰ ℓ ℓ)
  StateAlgCBPVComputationTerminalsⱽ ℓ B =
    EqTerminalⱽ→Terminalⱽ (StateAlgCBPVAssoc ℓ) (StateAlgCBPVᴰ ℓ ℓ)
      (EqPsh.UEⱽ→Reprⱽ _ (StateAlgCBPVIdR ℓ) ue)
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = StateAlgCBPVᴰ ℓ ℓ}
        {P = (∫C (StateAlgCBPV {ℓ = ℓ} .fst)) [-, (𝓒 , B) ]})
      (StateAlgCBPVIdR ℓ)
    ue .EqPsh.UEⱽ.v .fst _ = Unit* , isSetUnit*
    ue .EqPsh.UEⱽ.v .snd = Unitⱽ (B .snd) ℓ
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .fst _ _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .fst _ .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .fst _ .snd =
      !ⱽ (f .snd .snd) (Xᴰ .snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .snd .snd h =
      funExt₂ λ _ _ → refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .snd .snd h =
      ∫Homoᴰ≡ _ h (λ _ → isSetUnit*) (funExt₂ λ _ _ → refl)

  StateAlgCBPVComputationBinProductsⱽ : ∀ ℓ →
    ComputationBinProductsⱽ (StateAlgCBPVᴰ ℓ ℓ)
  StateAlgCBPVComputationBinProductsⱽ ℓ {B} B₁ᴰ B₂ᴰ =
    EqBinProductⱽ→BinProductⱽ (StateAlgCBPVAssoc ℓ) (StateAlgCBPVᴰ ℓ ℓ)
      (EqPsh.UEⱽ→Reprⱽ _ (StateAlgCBPVIdR ℓ) ue)
    where
    ue : EqPsh.UEⱽ
      (((StateAlgCBPVᴰ ℓ ℓ) EqPsh.[-][-, B₁ᴰ ]) EqPsh.×ⱽPsh
       ((StateAlgCBPVᴰ ℓ ℓ) EqPsh.[-][-, B₂ᴰ ]))
      (StateAlgCBPVIdR ℓ)
    ue .EqPsh.UEⱽ.v .fst x =
      (B₁ᴰ .fst x .fst × B₂ᴰ .fst x .fst) ,
      isSet× (B₁ᴰ .fst x .snd) (B₂ᴰ .fst x .snd)
    ue .EqPsh.UEⱽ.v .snd = Prodⱽ (B₁ᴰ .snd) (B₂ᴰ .snd)
    ue .EqPsh.UEⱽ.e .fst .fst _ = fst
    ue .EqPsh.UEⱽ.e .fst .snd = π₁ⱽ (B₁ᴰ .snd) (B₂ᴰ .snd)
    ue .EqPsh.UEⱽ.e .snd .fst _ = snd
    ue .EqPsh.UEⱽ.e .snd .snd = π₂ⱽ (B₁ᴰ .snd) (B₂ᴰ .snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .fst
      (p , q) x xᴰ = p x xᴰ , q x xᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .fst
      (p , q) .fst x xᴰ = p .fst x xᴰ , q .fst x xᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .fst
      (p , q) .snd =
        ×ⱽintroⱽ (B₁ᴰ .snd) (B₂ᴰ .snd) (f .snd .snd) (p .snd) (q .snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓥 , X) , Xᴰ , f) .snd .snd h = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso ((𝓒 , X) , Xᴰ , f) .snd .snd h =
      ∫Homoᴰ≡ _ h
        (λ x → isSet× (B₁ᴰ .fst x .snd) (B₂ᴰ .fst x .snd)) refl

  StateAlgCBPVVerticalCartesianLifts : ∀ ℓ k →
    hasVerticalCartesianLiftsAt (StateAlgCBPVᴰ ℓ ℓ) k
  StateAlgCBPVVerticalCartesianLifts ℓ 𝓥 {A} {B} f Bᴰ =
    EqCartesianLift→CartesianLift (StateAlgCBPVAssoc ℓ)
      (StateAlgCBPVᴰ ℓ ℓ) Bᴰ (𝓥 , A) (_ , f)
      (EqPsh.UEⱽ→Reprⱽ _ (StateAlgCBPVIdR ℓ) ue)
    where
    ue : EqPsh.CartesianLiftUE (StateAlgCBPVᴰ ℓ ℓ)
      (StateAlgCBPVAssoc ℓ) (StateAlgCBPVIdR ℓ) (_ , f) Bᴰ
    ue .EqPsh.UEⱽ.v x = Bᴰ (f x)
    ue .EqPsh.UEⱽ.e _ xᴰ = xᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , g) .fst h = h
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , g) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , g) .snd .snd _ = refl
  StateAlgCBPVVerticalCartesianLifts ℓ 𝓒 {A} {B} f Bᴰ =
    EqCartesianLift→CartesianLift (StateAlgCBPVAssoc ℓ)
      (StateAlgCBPVᴰ ℓ ℓ) Bᴰ (𝓒 , A) (_ , f)
      (EqPsh.UEⱽ→Reprⱽ _ (StateAlgCBPVIdR ℓ) ue)
    where
    pullᴰ : Fibers.ob[_] (StateAlgCBPVᴰ ℓ ℓ) (𝓒 , A)
    pullᴰ .fst x = Bᴰ .fst (f .fst x)
    pullᴰ .snd = pull (f .snd) (Bᴰ .snd) (B .fst .snd)
    ue : EqPsh.CartesianLiftUE (StateAlgCBPVᴰ ℓ ℓ)
      (StateAlgCBPVAssoc ℓ) (StateAlgCBPVIdR ℓ) (_ , f) Bᴰ
    ue .EqPsh.UEⱽ.v = pullᴰ
    ue .EqPsh.UEⱽ.e .fst _ xᴰ = xᴰ
    ue .EqPsh.UEⱽ.e .snd = π-pull (f .snd) (Bᴰ .snd) (B .fst .snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , g) .fst h = h
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , g) .fst h .fst = h .fst
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , g) .fst h .snd =
        pull-intro (f .snd) (Bᴰ .snd) (B .fst .snd) (g .snd .snd) (h .snd)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , g) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , g) .snd .fst h =
        ∫Homoᴰ≡ _ h (λ x → Bᴰ .fst x .snd) refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , g) .snd .snd _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , g) .snd .snd h =
        ∫Homoᴰ≡ _ h (λ x → Bᴰ .fst (f .fst x) .snd) refl

  StateAlgCBPVValueOpcartesianLifts : ∀ ℓ →
    hasVerticalOpcartesianLiftsAt (StateAlgCBPVᴰ ℓ ℓ) 𝓥
  StateAlgCBPVValueOpcartesianLifts ℓ {A} {B} f Aᴰ =
    EqCartesianLift→CartesianLift (StateAlgCBPVAssoc^op ℓ)
      ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰ) Aᴰ (𝓥 , B) (_ , f)
      (EqPsh.UEⱽ→Reprⱽ _ idR ue)
    where
    idR : EqPsh.EqIdR ((∫C (StateAlgCBPV {ℓ = ℓ} .fst)) ^op)
    idR {x = 𝓥 , X} {y = 𝓥 , Y} g = Eq.refl
    idR {x = 𝓒 , X} {y = 𝓥 , Y} g = Eq.refl
    idR {x = 𝓥 , X} {y = 𝓒 , Y} ()
    idR {x = 𝓒 , X} {y = 𝓒 , Y} g = Eq.refl
    ue : EqPsh.CartesianLiftUE ((StateAlgCBPVᴰ ℓ ℓ) ^opᴰ)
      (StateAlgCBPVAssoc^op ℓ) idR (_ , f) Aᴰ
    ue .EqPsh.UEⱽ.v b .fst =
      Σ[ a ∈ A .fst ] (f a ≡ b) × Aᴰ a .fst
    ue .EqPsh.UEⱽ.v b .snd =
      isSetΣ (A .snd) λ a →
        isSet× (isProp→isSet (B .snd _ _)) (Aᴰ a .snd)
    ue .EqPsh.UEⱽ.e a aᴰ = a , refl , aᴰ
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , g) .fst h b (a , p , aᴰ) =
        subst (λ b' → Xᴰ (g .snd b') .fst) p (h a aᴰ)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , g) .fst h b (a , p , aᴰ) =
        subst (λ b' → Xᴰ .fst (g .snd b') .fst) p (h a aᴰ)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , g) .snd .fst h =
      funExt₂ λ _ _ → transportRefl _
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , g) .snd .fst h =
      funExt₂ λ _ _ → transportRefl _
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓥 , X) , Xᴰ , g) .snd .snd h =
        funExt λ b → funExt λ { (a , p , aᴰ) →
          J (λ b' p' →
            subst (λ b'' → Xᴰ (g .snd b'') .fst) p'
              (h (f a) (a , refl , aᴰ)) ≡ h b' (a , p' , aᴰ))
            (transportRefl _) p }
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      ((𝓒 , X) , Xᴰ , g) .snd .snd h =
        funExt λ b → funExt λ { (a , p , aᴰ) →
          J (λ b' p' →
            subst (λ b'' → Xᴰ .fst (g .snd b'') .fst) p'
              (h (f a) (a , refl , aᴰ)) ≡ h b' (a , p' , aᴰ))
            (transportRefl _) p }
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
      .Homo.rd-hom _ _ _ _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .fst _ .snd
      .Homo.wt-hom _ _ _ _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd h =
      funExt λ _ → refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .snd h =
      ∫Homo≡ _ h isSetUnit* (funExt λ _ → refl)

  StateAlgComputationProductEqⱽ :
    ∀ B₁ B₂ → EqBinProductⱽ C {k = 𝓒} B₁ B₂
  StateAlgComputationProductEqⱽ B₁ B₂ =
    EqPsh.UEⱽ→Reprⱽ _ KIND-idR ue
    where
    pairC : ∀ {B : StateAlgebra ℓ} → StateAlgHom B B₁ → StateAlgHom B B₂ →
      StateAlgHom B (StateAlgProduct B₁ B₂)
    pairC p q .fst x = p .fst x , q .fst x
    pairC p q .snd .Homo.rd-hom xt xf rdtf e i =
      p .snd .Homo.rd-hom xt xf rdtf e i ,
      q .snd .Homo.rd-hom xt xf rdtf e i
    pairC p q .snd .Homo.wt-hom b x wtbx e i =
      p .snd .Homo.wt-hom b x wtbx e i ,
      q .snd .Homo.wt-hom b x wtbx e i

    proj₁C : StateAlgHom (StateAlgProduct B₁ B₂) B₁
    proj₁C .fst = fst
    proj₁C .snd .Homo.rd-hom _ _ _ p i = p i .fst
    proj₁C .snd .Homo.wt-hom _ _ _ p i = p i .fst

    proj₂C : StateAlgHom (StateAlgProduct B₁ B₂) B₂
    proj₂C .fst = snd
    proj₂C .snd .Homo.rd-hom _ _ _ p i = p i .snd
    proj₂C .snd .Homo.wt-hom _ _ _ p i = p i .snd

    ue : EqPsh.UEⱽ
      ((EqPsh._[-][-,_] C B₁) EqPsh.×ⱽPsh (EqPsh._[-][-,_] C B₂))
      KIND-idR
    ue .EqPsh.UEⱽ.v = StateAlgProduct B₁ B₂
    ue .EqPsh.UEⱽ.e .fst = proj₁C
    ue .EqPsh.UEⱽ.e .snd = proj₂C
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .fst
      (p , q) x = p x , q x
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .fst
      (p , q) = pairC p q
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .fst (p , q) =
      ΣPathP
        ( ∫Homo≡ _ p (B₁ .fst .snd) refl
        , ∫Homo≡ _ q (B₂ .fst .snd) refl)
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd _ =
      refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .snd h =
      ∫Homo≡ _ h
        (isSet× (B₁ .fst .snd) (B₂ .fst .snd)) refl

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

  StateAlgAddCBPVⱽ :
    AddCBPVCatⱽ (StateAlgAddCBPV .fst .fst) (ℓ-suc ℓ) ℓ
  StateAlgAddCBPVⱽ .fst = StateAlgCBPVⱽ
  StateAlgAddCBPVⱽ .snd .fst = StateAlgCBPVValueTerminalsⱽ ℓ
  StateAlgAddCBPVⱽ .snd .snd .fst = StateAlgCBPVValueBinProductsⱽ ℓ
  StateAlgAddCBPVⱽ .snd .snd .snd .fst =
    StateAlgCBPVVerticalCartesianLifts ℓ 𝓥
  StateAlgAddCBPVⱽ .snd .snd .snd .snd .fst =
    StateAlgCBPVValueInitialsEqⱽ ℓ
  StateAlgAddCBPVⱽ .snd .snd .snd .snd .snd .fst =
    StateAlgCBPVValueBinCoProductsEqⱽ ℓ
  StateAlgAddCBPVⱽ .snd .snd .snd .snd .snd .snd .fst =
    StateAlgCBPVValueOpcartesianLifts ℓ
  StateAlgAddCBPVⱽ .snd .snd .snd .snd .snd .snd .snd .fst =
    StateAlgCBPVComputationTerminalsⱽ ℓ
  StateAlgAddCBPVⱽ .snd .snd .snd .snd .snd .snd .snd .snd .fst =
    StateAlgCBPVComputationBinProductsⱽ ℓ
  StateAlgAddCBPVⱽ .snd .snd .snd .snd .snd .snd .snd .snd .snd =
    StateAlgCBPVVerticalCartesianLifts ℓ 𝓒
