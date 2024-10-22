{-
  Arrow category and sub-category of Isos as categories displayed over C × C.

  Universal property: a section of the Arrow bundle is a natural
  transformation between functors, section of the Iso bundle is a
  natural isomorphism

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Arrow.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.Graph
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.Constructions.TotalCategory
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Displayed.Fibration.TwoSided
open import Cubical.Categories.Displayed.Fibration.IsoFibration
open import Cubical.Categories.Displayed.Instances.Arrow.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

open isTwoSidedWeakFibration
open isTwoSidedWeakIsoFibration
open isIso
open Category
module _ (C : Category ℓC ℓC') where
  isTwoSidedWeakFibrationArrow
    : isTwoSidedWeakFibration {C = C}{D = C} (Arrow C)
  isTwoSidedWeakFibrationArrow = isTwoSidedWeakFibrationGraph (HomBif C)

  isTwoSidedWeakIsoFibrationIso
    : isTwoSidedWeakIsoFibration {C = C}{D = C} (Iso C)
  isTwoSidedWeakIsoFibrationIso .leftLifts p f = record
    { f*p = leftLift.f*p , ⋆Iso f p .snd
    ; π = leftLift.π , _
    ; wkUniversal = λ pf → (leftLift.wkUniversal (pf .fst)) , _
    }
    where
      leftLift = isTwoSidedWeakFibrationArrow .leftLifts (p .fst) (f .fst)
      module leftLift = WeakLeftCartesianLift leftLift
  isTwoSidedWeakIsoFibrationIso .rightLifts p f = record
    { pf* = rightLift.pf* , ⋆Iso p f .snd
    ; σ = rightLift.σ , _
    ; wkUniversal = λ pf → rightLift.wkUniversal (pf .fst) , _
    } where
      rightLift = isTwoSidedWeakFibrationArrow .rightLifts (p .fst) (f .fst)
      module rightLift = WeakRightOpCartesianLift rightLift

  isIsoFibrationIso : isWeakIsoFibration (Iso C)
  isIsoFibrationIso {c = x , y}{c' = x' , y'} x'≅y' fg = record
    { f*cᴰ = ⋆Iso x≅x' (⋆Iso x'≅y' y'≅y)
    ; π = sym (C .⋆IdR _)
      ∙ C .⋆Assoc _ _ _
      ∙ cong₂ (seq' C) refl
        (cong₂ (seq' C) refl (sym (y'≅y .snd .ret)) ∙ sym (C .⋆Assoc _ _ _))
      ∙ sym (C .⋆Assoc _ _ _)
      , _
    ; σ = sym (C .⋆Assoc _ _ _)
      ∙ cong₂ (comp' C) refl (x≅x' .snd .sec)
      ∙ C .⋆IdL _
      , _
    }
    where
      x≅x' = SplitCatIso× C C fg .fst
      y'≅y = invIso (SplitCatIso× C C fg .snd)
