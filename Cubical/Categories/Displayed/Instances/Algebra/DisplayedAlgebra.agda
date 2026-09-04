{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Algebra.DisplayedAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory as TotalCat
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebra.Algebra
open import Cubical.Categories.Displayed.Instances.Reindex.Eq.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.TotalCategory
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh

open import Cubical.Algebra.Signature.Base

module _ {ℓO ℓA}(Sig : Signature ℓO ℓA) where
  open Signature Sig
  SETᴰOverALG : ∀ ℓ ℓᴰ → Categoryᴰ (ALG Sig ℓ) _ _
  SETᴰOverALG ℓ ℓᴰ = (EqReindexWithLaws.reindex
      (SETᴰ ℓ ℓᴰ)
      (ALGForget Sig)
      Eq.refl
      (λ _ _ → Eq.refl)
      (λ _ → refl)
      (λ _ → refl)
      (λ _ _ _ → refl))

  ALG×SETᴰ : ∀ ℓ ℓᴰ → Category _ _
  ALG×SETᴰ ℓ ℓᴰ = ∫C (SETᴰOverALG ℓ ℓᴰ)

  ALGᴰOver : ∀ ℓ ℓᴰ → Categoryᴰ (ALG×SETᴰ ℓ ℓᴰ) _ _
  ALGᴰOver ℓ ℓᴰ .Categoryᴰ.ob[_] XAXᴰ =
    AlgebraᴰWithCarrier (_ , XAXᴰ .fst .snd) (⟨_⟩ ∘ XAXᴰ .snd)
  ALGᴰOver ℓ ℓᴰ .Categoryᴰ.Hom[_][_,_] (ϕ , fᴰ) Aᴰ Bᴰ =
    isHomoᴰSimpl ϕ (_ , Aᴰ) (_ , Bᴰ) fᴰ
  ALGᴰOver ℓ ℓᴰ .Categoryᴰ.idᴰ = idHomoᴰ .snd
  ALGᴰOver ℓ ℓᴰ .Categoryᴰ._⋆ᴰ_ {yᴰ = Bᴰ}{zᴰ = Cᴰ} ϕᴰ ψᴰ =
    (_⋆Hᴰ_ {Cᴰ = _ , Cᴰ} (_ , ϕᴰ) (_ , ψᴰ)) .snd
  ALGᴰOver ℓ ℓᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
  ALGᴰOver ℓ ℓᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
  ALGᴰOver ℓ ℓᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
  ALGᴰOver ℓ ℓᴰ .Categoryᴰ.isSetHomᴰ {y = (Y , B) , Yᴰ} =
    isProp→isSet
      (isPropΠ λ _ → isPropΠ6 λ _ _ _ _ _ _ → Yᴰ _ .snd _ _)

  ALGᴰ : ∀ ℓ ℓᴰ → Categoryᴰ (ALG Sig ℓ) _ _
  ALGᴰ ℓ ℓᴰ = ∫Cᴰ (SETᴰOverALG ℓ ℓᴰ) (ALGᴰOver ℓ ℓᴰ)

  module _ {ℓ ℓᴰ} {X Y : ALG Sig ℓ .Category.ob}
    {Xᴰ : Categoryᴰ.ob[_] (ALGᴰ ℓ ℓᴰ) X}
    {Yᴰ : Categoryᴰ.ob[_] (ALGᴰ ℓ ℓᴰ) Y}
    {f : ALG Sig ℓ [ X , Y ]}
    (fᴰ gᴰ : Categoryᴰ.Hom[_][_,_] (ALGᴰ ℓ ℓᴰ) f Xᴰ Yᴰ) where
    ALGᴰHomo≡ : fᴰ .fst ≡ gᴰ .fst → fᴰ ≡ gᴰ
    ALGᴰHomo≡ fᴰ≡gᴰ i .fst = fᴰ≡gᴰ i
    ALGᴰHomo≡ fᴰ≡gᴰ i .snd =
      isProp→PathP
        {B = λ i → Categoryᴰ.Hom[_][_,_] (ALGᴰOver ℓ ℓᴰ)
          (f , fᴰ≡gᴰ i) (Xᴰ .snd) (Yᴰ .snd)}
        (λ _ → isPropΠ6 λ _ _ _ _ _ _ →
          isPropΠ λ _ → Yᴰ .fst _ .snd _ _)
        (fᴰ .snd) (gᴰ .snd) i

  private
    ALGIdR : ∀ {ℓ} → EqPsh.EqIdR (ALG Sig ℓ)
    ALGIdR _ = Eq.refl

  TerminalsEqⱽALGᴰ : ∀ {ℓ ℓᴰ} → EqPsh.Terminalsⱽ (ALGᴰ ℓ ℓᴰ)
  TerminalsEqⱽALGᴰ {ℓ = ℓ} {ℓᴰ = ℓᴰ} X =
    EqPsh.UEⱽ→Reprⱽ _ ALGIdR ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = ALGᴰ ℓ ℓᴰ} {P = (ALG Sig ℓ) [-, X ]})
      ALGIdR
    ue .EqPsh.UEⱽ.v = (λ _ → Unit* , isSetUnit*) , ⊤*ⱽ .snd
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .fst _ .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .fst _ .snd _ _ _ _ _ _ _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .snd .snd h = ALGᴰHomo≡ _ h (funExt λ _ → funExt λ _ → refl)

  BinProductsEqⱽALGᴰ : ∀ {ℓ ℓᴰ} → EqPsh.BinProductsⱽ (ALGᴰ ℓ ℓᴰ)
  BinProductsEqⱽALGᴰ {ℓ = ℓ} {ℓᴰ = ℓᴰ} {x = X}
    (Xᴰ , Aᴰ) (Yᴰ , Bᴰ) = EqPsh.UEⱽ→Reprⱽ _ ALGIdR ue
    where
    ue : EqPsh.UEⱽ
      (((ALGᴰ ℓ ℓᴰ EqPsh.[-][-, Xᴰ , Aᴰ ]) EqPsh.×ⱽPsh
        (ALGᴰ ℓ ℓᴰ EqPsh.[-][-, Yᴰ , Bᴰ ])))
      ALGIdR
    ue .EqPsh.UEⱽ.v =
      (λ a → (⟨ Xᴰ a ⟩ × ⟨ Yᴰ a ⟩) , isSet× (Xᴰ a .snd) (Yᴰ a .snd)) ,
      ((_ , Aᴰ) ×ⱽ (_ , Bᴰ)) .snd
    ue .EqPsh.UEⱽ.e .fst .fst _ z = z .fst
    ue .EqPsh.UEⱽ.e .fst .snd _ _ _ _ _ _ p = cong fst p
    ue .EqPsh.UEⱽ.e .snd .fst _ z = z .snd
    ue .EqPsh.UEⱽ.e .snd .snd _ _ _ _ _ _ p = cong snd p
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .fst (ϕᴰ , ψᴰ) .fst a z = ϕᴰ .fst a z , ψᴰ .fst a z
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .fst (ϕᴰ , ψᴰ) .snd
      op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ i =
        ϕᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ i ,
        ψᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ i
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .snd .snd h = ALGᴰHomo≡ _ h refl

  TerminalsⱽALGᴰ : ∀ {ℓ ℓᴰ} → EqPsh.Terminalsⱽ (ALGᴰ ℓ ℓᴰ)
  TerminalsⱽALGᴰ = TerminalsEqⱽALGᴰ

  BinProductsⱽALGᴰ : ∀ {ℓ ℓᴰ} → EqPsh.BinProductsⱽ (ALGᴰ ℓ ℓᴰ)
  BinProductsⱽALGᴰ = BinProductsEqⱽALGᴰ
