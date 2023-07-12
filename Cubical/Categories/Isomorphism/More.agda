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
open import Cubical.Foundations.Isomorphism.More

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open isUnivalent
module _ {C : Category ℓC ℓC'} (isUnivC : isUnivalent C) where
  op-Iso-pathToIso : ∀ {x y : C .ob} (p : x ≡ y)
                   → op-Iso (pathToIso {C = C} p) ≡ pathToIso {C = C ^op} p
  op-Iso-pathToIso =
    J (λ y p → op-Iso (pathToIso {C = C} p) ≡ pathToIso {C = C ^op} p)
      (CatIso≡ _ _ refl)

  op-Iso-pathToIso' : ∀ {x y : C .ob} (p : x ≡ y)
                   → op-Iso (pathToIso {C = C ^op} p) ≡ pathToIso {C = C} p
  op-Iso-pathToIso' =
    J (λ y p → op-Iso (pathToIso {C = C ^op} p) ≡ pathToIso {C = C} p)
      (CatIso≡ _ _ refl)

  isUnivalentOp : isUnivalent (C ^op)
  isUnivalentOp .univ x y = isIsoToIsEquiv
    ( (λ f^op → CatIsoToPath isUnivC (op-Iso f^op))
    , (λ f^op → CatIso≡ _ _
        (cong fst
        (cong op-Iso ((secEq (univEquiv isUnivC _ _) (op-Iso f^op))))))
    , λ p → cong (CatIsoToPath isUnivC) (op-Iso-pathToIso' p)
        ∙ retEq (univEquiv isUnivC _ _) p)

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
