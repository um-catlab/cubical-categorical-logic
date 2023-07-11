{-# OPTIONS --safe #-}
module Cubical.Categories.Isomorphism.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Function
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Isomorphism

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open isUnivalent
module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{F : Functor C D} where
  module _ (isUnivC : isUnivalent C) (isUnivD : isUnivalent D) where
    isoToPathC = CatIsoToPath isUnivC
    isoToPathD = CatIsoToPath isUnivD

    F-isoToPath : {x y : C .ob} → (f : CatIso C x y) →
      isoToPathD (F-Iso {F = F} f) ≡ cong (F .F-ob) (isoToPathC f)
    F-isoToPath f = isoFunInjective (equivToIso (univEquiv isUnivD _ _)) _ _
      ( secEq (univEquiv isUnivD _ _) _
      ∙ sym (sym (F-pathToIso {F = F} (isoToPathC f))
      ∙ cong (F-Iso {F = F}) (secEq (univEquiv isUnivC _ _) f)))
