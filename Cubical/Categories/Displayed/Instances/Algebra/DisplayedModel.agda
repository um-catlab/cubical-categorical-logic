{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Algebra.DisplayedModel where

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
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Instances.Reindex.Eq.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.TotalCategory
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh

open import Cubical.Algebra.Theory.Base
  hiding (ℓ; ℓᴰ; ℓᴰᴰ; ℓ'; ℓᴰ'; ℓᴰᴰ'; ℓ''; ℓᴰ''; ℓO; ℓA; ℓE)

module _ {ℓO ℓA ℓE ℓEA} (T : Theory ℓO ℓA ℓE ℓEA) where
  open Theory T

  private
    MODELOb→Model : ∀ {ℓ} → MODEL T ℓ .Category.ob → Model ℓ
    MODELOb→Model M .fst = ⟨ M .fst ⟩ , M .snd .fst
    MODELOb→Model M .snd .fst = M .snd .snd
    MODELOb→Model M .snd .snd = M .fst .snd

  SETᴰOverMODEL : ∀ ℓ ℓᴰ → Categoryᴰ (MODEL T ℓ) _ _
  SETᴰOverMODEL ℓ ℓᴰ = EqReindexWithLaws.reindex
    (SETᴰ ℓ ℓᴰ)
    (MODELForget T)
    Eq.refl
    (λ _ _ → Eq.refl)
    (λ _ → refl)
    (λ _ → refl)
    (λ _ _ _ → refl)

  MODEL×SETᴰ : ∀ ℓ ℓᴰ → Category _ _
  MODEL×SETᴰ ℓ ℓᴰ = ∫C (SETᴰOverMODEL ℓ ℓᴰ)

  MODELᴰOver : ∀ ℓ ℓᴰ → Categoryᴰ (MODEL×SETᴰ ℓ ℓᴰ) _ _
  MODELᴰOver ℓ ℓᴰ .Categoryᴰ.ob[_] XMXᴰ =
    ModelᴰWithCarrier
      (MODELOb→Model (XMXᴰ .fst))
      (⟨_⟩ ∘ XMXᴰ .snd)
  MODELᴰOver ℓ ℓᴰ .Categoryᴰ.Hom[_][_,_] (ϕ , fᴰ) Aᴰ Bᴰ =
    isHomoᴰSimpl ϕ (_ , Aᴰ .fst) (_ , Bᴰ .fst) fᴰ
  MODELᴰOver ℓ ℓᴰ .Categoryᴰ.idᴰ = idHomoᴰ .snd
  MODELᴰOver ℓ ℓᴰ .Categoryᴰ._⋆ᴰ_ {yᴰ = Bᴰ} {zᴰ = Cᴰ} ϕᴰ ψᴰ =
    (_⋆Hᴰ_ {Cᴰ = _ , Cᴰ .fst} (_ , ϕᴰ) (_ , ψᴰ)) .snd
  MODELᴰOver ℓ ℓᴰ .Categoryᴰ.⋆IdLᴰ _ = refl
  MODELᴰOver ℓ ℓᴰ .Categoryᴰ.⋆IdRᴰ _ = refl
  MODELᴰOver ℓ ℓᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = refl
  MODELᴰOver ℓ ℓᴰ .Categoryᴰ.isSetHomᴰ {y = (Y , B) , Yᴰ} =
    isProp→isSet
      (isPropΠ λ _ → isPropΠ6 λ _ _ _ _ _ _ → Yᴰ _ .snd _ _)

  MODELᴰ : ∀ ℓ ℓᴰ → Categoryᴰ (MODEL T ℓ) _ _
  MODELᴰ ℓ ℓᴰ = ∫Cᴰ (SETᴰOverMODEL ℓ ℓᴰ) (MODELᴰOver ℓ ℓᴰ)

  module _ {ℓ ℓᴰ} {X Y : MODEL T ℓ .Category.ob}
    {Xᴰ : Categoryᴰ.ob[_] (MODELᴰ ℓ ℓᴰ) X}
    {Yᴰ : Categoryᴰ.ob[_] (MODELᴰ ℓ ℓᴰ) Y}
    {f : MODEL T ℓ [ X , Y ]}
    (fᴰ gᴰ : Categoryᴰ.Hom[_][_,_] (MODELᴰ ℓ ℓᴰ) f Xᴰ Yᴰ) where
    MODELᴰHomo≡ : fᴰ .fst ≡ gᴰ .fst → fᴰ ≡ gᴰ
    MODELᴰHomo≡ fᴰ≡gᴰ i .fst = fᴰ≡gᴰ i
    MODELᴰHomo≡ fᴰ≡gᴰ i .snd =
      isProp→PathP
        {B = λ i → Categoryᴰ.Hom[_][_,_] (MODELᴰOver ℓ ℓᴰ)
          (f , fᴰ≡gᴰ i) (Xᴰ .snd) (Yᴰ .snd)}
        (λ _ → isPropΠ6 λ _ _ _ _ _ _ →
          isPropΠ λ _ → Yᴰ .fst _ .snd _ _)
        (fᴰ .snd) (gᴰ .snd) i

  private
    MODELIdR : ∀ {ℓ} → EqPsh.EqIdR (MODEL T ℓ)
    MODELIdR _ = Eq.refl

  TerminalsEqⱽMODELᴰ : ∀ {ℓ ℓᴰ} → EqPsh.Terminalsⱽ (MODELᴰ ℓ ℓᴰ)
  TerminalsEqⱽMODELᴰ {ℓ = ℓ} {ℓᴰ = ℓᴰ} X =
    EqPsh.UEⱽ→Reprⱽ _ MODELIdR ue
    where
    ue : EqPsh.UEⱽ
      (EqPsh.UnitⱽPsh {Cᴰ = MODELᴰ ℓ ℓᴰ} {P = (MODEL T ℓ) [-, X ]})
      MODELIdR
    ue .EqPsh.UEⱽ.v =
      (λ _ → Unit* , isSetUnit*) ,
      (⊤*ⱽ .snd , λ _ _ _ → isProp→PathP (λ _ → isPropUnit*) _ _)
    ue .EqPsh.UEⱽ.e = tt
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .fst _ .fst _ _ = tt*
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .fst _ .snd _ _ _ _ _ _ _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .snd .snd h = MODELᴰHomo≡ _ h (funExt λ _ → funExt λ _ → refl)

  TerminalsⱽMODELᴰ : ∀ {ℓ ℓᴰ} → EqPsh.Terminalsⱽ (MODELᴰ ℓ ℓᴰ)
  TerminalsⱽMODELᴰ = TerminalsEqⱽMODELᴰ

  private
    interpProductᴰ : ∀ {ℓ ℓᴰ ℓV} {M : MODEL T ℓ .Category.ob}
      (Mᴰ Nᴰ : Categoryᴰ.ob[_] (MODELᴰ ℓ ℓᴰ) M)
      {V : Type ℓV}
      (ρ : V → ⟨ M .fst ⟩)
      (ρᴰ : (v : V) → ⟨ Mᴰ .fst (ρ v) ⟩ × ⟨ Nᴰ .fst (ρ v) ⟩)
      (t : |FreeAlgebra| V)
      → interpᴰ
          ((_ , Mᴰ .snd .fst) ×ⱽ (_ , Nᴰ .snd .fst))
          ρ ρᴰ t
        ≡ ( interpᴰ (_ , Mᴰ .snd .fst) ρ (λ v → ρᴰ v .fst) t
          , interpᴰ (_ , Nᴰ .snd .fst) ρ (λ v → ρᴰ v .snd) t)
    interpProductᴰ Mᴰ Nᴰ ρ ρᴰ (var v) = refl
    interpProductᴰ {M = M} Mᴰ Nᴰ ρ ρᴰ (app op γ) =
      cong₂ _,_
        (cong
          (λ γᴰ → Mᴰ .snd .fst op
            (λ v → interp (MODELOb→Model M .fst) ρ (γ v)) γᴰ
            (interp (MODELOb→Model M .fst) ρ (app op γ))
            (recFA (MODELOb→Model M .fst) ρ .snd
              op γ (app op γ) refl))
          (funExt λ v →
            cong fst (interpProductᴰ Mᴰ Nᴰ ρ ρᴰ (γ v))))
        (cong
          (λ γᴰ → Nᴰ .snd .fst op
            (λ v → interp (MODELOb→Model M .fst) ρ (γ v)) γᴰ
            (interp (MODELOb→Model M .fst) ρ (app op γ))
            (recFA (MODELOb→Model M .fst) ρ .snd
              op γ (app op γ) refl))
          (funExt λ v →
            cong snd (interpProductᴰ Mᴰ Nᴰ ρ ρᴰ (γ v))))

  BinProductsEqⱽMODELᴰ : ∀ {ℓ ℓᴰ} →
    EqPsh.BinProductsⱽ (MODELᴰ ℓ ℓᴰ)
  BinProductsEqⱽMODELᴰ {ℓ = ℓ} {ℓᴰ = ℓᴰ} {x = X}
    (Xᴰ , Aᴰ) (Yᴰ , Bᴰ) = EqPsh.UEⱽ→Reprⱽ _ MODELIdR ue
    where
    ue : EqPsh.UEⱽ
      (((MODELᴰ ℓ ℓᴰ EqPsh.[-][-, Xᴰ , Aᴰ ]) EqPsh.×ⱽPsh
        (MODELᴰ ℓ ℓᴰ EqPsh.[-][-, Yᴰ , Bᴰ ])))
      MODELIdR
    ue .EqPsh.UEⱽ.v =
      (λ a →
        (⟨ Xᴰ a ⟩ × ⟨ Yᴰ a ⟩) ,
        isSet× (Xᴰ a .snd) (Yᴰ a .snd)) ,
      ( ((_ , Aᴰ .fst) ×ⱽ (_ , Bᴰ .fst)) .snd
      , λ e ρ ρᴰ →
          interpProductᴰ (Xᴰ , Aᴰ) (Yᴰ , Bᴰ) ρ ρᴰ (lhs e)
          ◁ (λ i →
              Aᴰ .snd e ρ (λ v → ρᴰ v .fst) i ,
              Bᴰ .snd e ρ (λ v → ρᴰ v .snd) i)
          ▷ sym
              (interpProductᴰ (Xᴰ , Aᴰ) (Yᴰ , Bᴰ) ρ ρᴰ (rhs e)))
    ue .EqPsh.UEⱽ.e .fst .fst _ z = z .fst
    ue .EqPsh.UEⱽ.e .fst .snd _ _ _ _ _ _ p = cong fst p
    ue .EqPsh.UEⱽ.e .snd .fst _ z = z .snd
    ue .EqPsh.UEⱽ.e .snd .snd _ _ _ _ _ _ p = cong snd p
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .fst (ϕᴰ , ψᴰ) .fst a z = ϕᴰ .fst a z , ψᴰ .fst a z
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .fst (ϕᴰ , ψᴰ) .snd
      op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ i =
        ϕᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
          op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ i ,
        ψᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
          op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ i
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .snd .fst _ = refl
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
      _ .snd .snd h = MODELᴰHomo≡ _ h refl

  BinProductsⱽMODELᴰ : ∀ {ℓ ℓᴰ} → EqPsh.BinProductsⱽ (MODELᴰ ℓ ℓᴰ)
  BinProductsⱽMODELᴰ = BinProductsEqⱽMODELᴰ
