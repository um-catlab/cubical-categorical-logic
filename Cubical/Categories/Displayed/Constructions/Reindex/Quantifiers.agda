{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
{-
  Sufficient conditions for Reindexed displayed category to have (universal) quantifiers
-}
module Cubical.Categories.Displayed.Constructions.Reindex.Quantifiers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Base
  hiding (π; reindex)
import Cubical.Categories.Displayed.Constructions.Reindex.Limits as Limits
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.BinProduct.Fiberwise
open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Quantifiers

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {c : C .Category.ob}
  (-×c : BinProductsWith C c)
  (-×Fc : BinProductsWith D (F ⟅ c ⟆))
  (F-× : preservesProvidedBinProductsWith F -×c)
  (isFibDᴰ : isFibration Dᴰ)
  where

  private
    module -×c = BinProductsWithNotation -×c
    module -×Fc = BinProductsWithNotation -×Fc
    module D = Category D
    module Dᴰ = Fibers Dᴰ
    module F*Dᴰ = Fibers (Base.reindex Dᴰ F)
    module isFibDᴰ = isFibrationNotation _ isFibDᴰ
    isFibF*Dᴰ = isFibrationReindex Dᴰ F isFibDᴰ
    module isFibF*Dᴰ = isFibrationNotation _ isFibF*Dᴰ
  module _ {Γ} {dᴰ : F*Dᴰ.ob[ Γ -×c.×a ]} where
    module F⟨Γ×c⟩ = BinProductNotation (preservesUniversalElement→UniversalElement (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))
    
    module _ (∀dᴰ : UniversalQuantifier -×Fc isFibDᴰ (isFibDᴰ.f*yᴰ dᴰ (-×Fc.π₁ F⟨Γ×c⟩.,p -×Fc.π₂ ))) where
      private
        module ∀dᴰ = UniversalQuantifierNotation _ _ ∀dᴰ
      open UniversalElementⱽ
      open Functor
      ∀Reindex : UniversalQuantifier -×c isFibF*Dᴰ dᴰ
      ∀Reindex .vertexⱽ = ∀dᴰ.vert
      -- want: Dᴰ [ F ⟪ π₁ ⋆ id ,p π₂ ⟫ ][ F ⟪ π₁ ⟫* ∀dᴰ , dᴰ ]
      -- have: Dᴰ [ (π₁ ⋆ id) ,p π₂ ][ π₁* ∀dᴰ, (π₁ ,p π₂)* dᴰ ]
      ∀Reindex .elementⱽ = Dᴰ.reind
        (D.⟨ refl ⟩⋆⟨ D.⟨ -×Fc.×aF .F-id ⟩⋆⟨ refl ⟩ ∙ D.⋆IdL _ ⟩
        ∙ F⟨Γ×c⟩.×ue.intro-natural
        ∙ F⟨Γ×c⟩.⟨ -×Fc.×β₁ ⟩,p⟨ -×Fc.×β₂ ⟩
        ∙ (sym $ F⟨Γ×c⟩.×ue.weak-η)
        ∙ (sym $ F .F-id) ∙ cong (F .F-hom) (sym $ -×c.×aF .F-id))
        (isFibDᴰ.introCL _ _ (Dᴰ.reind
          (sym $ -×Fc.×β₁) $
          isFibF*Dᴰ.π ∀dᴰ.vert (fst -×c.×ue.element) )
        Dᴰ.⋆ᴰ ∀dᴰ.app
        Dᴰ.⋆ᴰ isFibDᴰ.π _ _)
      ∀Reindex .universalⱽ = {!!}
  
module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {c : C .Category.ob}
  (bpC : BinProducts C)
  (bpD : BinProducts D)
  (F-× : preservesProvidedBinProducts F bpC)
  (isFibDᴰ : isFibration Dᴰ)
  where
  ∀sReindex : UniversalQuantifiers bpD isFibDᴰ
    → UniversalQuantifiers bpC (isFibrationReindex Dᴰ F isFibDᴰ)
  ∀sReindex ∀sD a Γ pᴰ =
    ∀Reindex
      (λ c₁ → bpC (c₁ , a))
      (λ c₁ → bpD (c₁ , Functor.F-ob F a))
      (λ c' → F-× c' a)
      isFibDᴰ
      (∀sD _ _ _)
