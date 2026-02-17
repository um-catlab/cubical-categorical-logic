{-
  An end of an endo-profunctor F : C -[ ℓR ]-> C
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.UniversalConstructions.End where


open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Bifunctors
open import Cubical.Categories.Constructions.BinProduct.Redundant as Tensor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Profunctor.Homomorphism.NaturalElement
open import Cubical.Categories.Profunctor.Hom
open import Cubical.Categories.Bifunctor as Redundant


private
  variable
    ℓC ℓC' ℓD ℓD' ℓP : Level

open Category
module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (F : Bifunctor (C ^op) C D)
   where

  -- d -> End F =~ NatElt (D [ d , F - = ])
  End-Spec : Presheaf D _
  End-Spec = NATURAL-ELEMENTS ∘F UNCURRY-BIFUNCTOR _ _ _ ∘F
    CurryBifunctor (Functor→Bifunctor (CurryBifunctor (assoc-bif⁻
      (HomR D ∘Fr Tensor.rec _ _ F))))

  End : Type _
  End = UniversalElement D End-Spec
