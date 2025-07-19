{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Graph.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Fibration.TwoSided
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.Graph.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level

open Category
open Functor
open isTwoSidedWeakFibration
open WeakLeftCartesianLift
open WeakRightOpCartesianLift
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
         (R : C o-[ ℓS ]-* D)
         where
  open Bifunctor

  private
    TabR = Graph R

  isTwoSidedWeakFibrationGraph
    : isTwoSidedWeakFibration {C = C}{D = D} (Graph R)
  isTwoSidedWeakFibrationGraph .leftLifts p f .f*p = f ⋆l⟨ R ⟩ p
  isTwoSidedWeakFibrationGraph .leftLifts p f .π = sym (relSeqRId R _)
  isTwoSidedWeakFibrationGraph .leftLifts p f .wkUniversal pf =
    sym (profAssocL R _ _ _) ∙ pf
  isTwoSidedWeakFibrationGraph .rightLifts p f .pf* = p ⋆r⟨ R ⟩ f
  isTwoSidedWeakFibrationGraph .rightLifts p f .σ = relSeqLId R _
  isTwoSidedWeakFibrationGraph .rightLifts p f .wkUniversal pf =
    pf ∙ profAssocR R _ _ _
