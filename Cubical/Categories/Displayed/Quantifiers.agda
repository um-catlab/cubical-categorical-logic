{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Quantifiers where

open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Constructions.Slice as Slice
open import Cubical.Categories.Displayed.Constructions.TotalCategory as ∫ᴰ
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf

-- The universal/pi and existential/weak sigma type are defined as
-- left and right adjoints to a "weakening" functor
--
-- Cᴰ(x × y) → Cᴰ x
--     |        |
-- x:C , y:C → x:C

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (bp : BinProducts C)
  -- This is an overly strong assumption for the construction, we only
  -- need pullbacks of π₁ . Not clear how to weaken it based on the current impl

  -- should we replace this with isFibration?
  (isFibration : isFibration' Cᴰ)
  where
  open BinProductsNotation bp
  private
    bpF = (BinProductF' C bp)
    Cᴰ[a×b] = reindex Cᴰ bpF
    Cᴰ[a] = reindex Cᴰ (Fst C C)
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ

  π₁Fᴰ : Functorᴰ bpF Cᴰ[a] (C /C Cᴰ)
  π₁Fᴰ = Slice.introF C Cᴰ
    (Fst C C)
    (Reindex.π Cᴰ (Fst C C))
    π₁Nat

  weakenⱽ : Functorⱽ {C = C ×C C} Cᴰ[a] Cᴰ[a×b]
  weakenⱽ = Reindex.introF _ (reindF' _ Eq.refl Eq.refl
    (CartesianLift'F Cᴰ isFibration ∘Fⱽᴰ π₁Fᴰ))

  {- Intuitively:
     f : C [ Γ , a ]
     Cᴰ [ f ][ Γᴰ , ∀ pᴰ ] ≅ Cᴰ [ f × b ][ π₁* Γᴰ , pᴰ ]
     with universal elt
     app : Cᴰ [ a × b ][ π₁* (∀ pᴰ) , pᴰ ]
  -}
  UniversalQuantifier : ∀ {a b} (p : Cᴰ.ob[ a × b ]) → Type _
  UniversalQuantifier = RightAdjointAtⱽ weakenⱽ

  UniversalQuantifiers : Type _
  UniversalQuantifiers = RightAdjointⱽ weakenⱽ

  -- TODO: it may be useful to prove the following:
  -- This definition includes the Beck condition that the quantifier
  -- is preserved by cartesian lifts, i.e., that quantifiers commute
  -- with substitution
  -- Cᴰ [ f ][ Γᴰ , g* (∀ pᴰ) ]
  -- ≅ Cᴰ [ f ⋆ g ][ Γᴰ , ∀ pᴰ ]
  -- ≅ Cᴰ [ f ⋆ g ][ Γᴰ , ∀ pᴰ ]
  -- ≅ Cᴰ [ (f ⋆ g) × b ][ π₁* Γᴰ , pᴰ ]
  -- ≅ Cᴰ [ (f × b) ⋆ (g × b) ][ π₁* Γᴰ , pᴰ ]
  -- ≅ Cᴰ [ (f × b) ][ π₁* Γᴰ , (g ⋆ b)* pᴰ ]
  -- ≅ Cᴰ [ f ][ Γᴰ , ∀ (g ⋆ b)* pᴰ ]

  -- TODO: define Existential Quantifier/weak Sigma as LeftAdjoint

  -- TODO: UniversalQuantifier(s) Notation
  module UniversalQuantifierNotation {a b} {pᴰ : Cᴰ.ob[ a × b ]}
    (∀pᴰ : UniversalQuantifier pᴰ) where
    module ∀ueⱽ = UniversalElementⱽ ∀pᴰ
    app : Cᴰ [ C.id ×p C.id ][ Functorᴰ.F-obᴰ (weakenⱽ ^opFⱽ) ∀ueⱽ.vertexᴰ , pᴰ ]
    app = ∀ueⱽ.elementᴰ
