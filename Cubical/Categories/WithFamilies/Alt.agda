{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.WithFamilies.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory as ∫
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Instances.Terminal.More
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration

open Category
open NatTrans
open Bifunctorᴰ
open Functorᴰ

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

-- Displayed category with "points"
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Fibers Cᴰ
    module C = Category C
  -- γ : C [ Δ , Γ ]      A : Cᴰ.ob[ Γ ]
  --------------------------------------
  -- M : Point[ γ ][ A ]
  --
  -- A term is a "vertical" Point[ id ][ A ]
  Families : (ℓS : Level) → Type _
  Families ℓS = Profunctorⱽ Cᴰ (Unitᴰ C) ℓS

  module _ (Fam : Families ℓS) where
    -- CompPush Γ A Δ = Σ[ γ : C [ Δ , Γ ] ] Families[ γ ][ A ]
    ComprehensionPsh : ∀ (Γ : C .ob)(A : Cᴰ.ob[ Γ ]) → Presheaf C (ℓ-max ℓC' ℓS)
    ComprehensionPsh Γ A = ΣF ∘F intro (C [-, Γ ])
      (compFunctorᴰGlobalSection (Fam .F-obᴰ {x = Γ} A ∘Fᴰⱽ Unitᴰ^op→^opᴰ ) ttS)

    -- Δ → Γ , x:A ≅ 
    FamComprehension : (Γ : C .ob)(A : Cᴰ.ob[ Γ ]) → Type _
    FamComprehension Γ A = UniversalElement C (ComprehensionPsh Γ A)

  CwFStr : (ℓS : Level) → Type _
  CwFStr ℓS =
    Σ[ Fam ∈ Families ℓS ]
    (∀ Γ A → FamComprehension Fam Γ A)
    × isFibration Cᴰ

  -- Tm [ γ ][ Σ[ x ∈ A ] B ]
  -- ≅ (M : Tm[ γ ][ A ]) × Tm[ γ , M ][ B ]
  --
  -- Cᴰ [ γ ][ C , Σ[ x ∈ A ] B ] ≅ (f : Cᴰ [ γ ][ C , A ]) × 
  --
  Tm [ γ ][ Π[ x ∈ A ] B ]
  ≅ Tm[ ]

-- Tm : Functorᴰ Cᴰ SETᴰ
-- Tm [ γ ][ A ]
--
--
-- δ : C [ Θ , Δ]  M : Tm [ γ ][ A ]
-- -------------------------------------
--       M[δ] : 

-- Δ → Γ × A

-- CwF : (ℓC ℓC' ℓT ℓT' : Level) → Type _
