-- Any functor U : 𝓒 → 𝓥 induces a CBPV model that has U, and if it
-- has a left adjoint the model has F.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.FromU where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Opposite
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.FromProf

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} {V : Category ℓ ℓ'}
  (U : Functor C V) (F : LeftAdjoint U) where

  hasFEq-U→CBPV : hasFEq (U→CBPV U)
  hasFEq-U→CBPV A = EqPsh.UEⱽ→Reprⱽ _ (λ _ → Eq.refl) ue
    where
    ue : EqPsh.CartesianLiftUE ((U→CBPV U) ^opᴰ) KIND^opAssoc
      (λ _ → Eq.refl) _ A
    ue .EqPsh.UEⱽ.v = F A .UniversalElement.vertex
    ue .EqPsh.UEⱽ.e = F A .UniversalElement.element
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓥 , _ , ())
    ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso (𝓒 , B , _) =
      isEquivToIsIso _ (F A .UniversalElement.universal B)

  U→MultCBPVEq : MultCBPVCatEq ℓ ℓ'
  U→MultCBPVEq = U→CBPV U , hasUEq-U→CBPV U , hasFEq-U→CBPV

  U→MultCBPV : MultCBPVCat ℓ ℓ'
  U→MultCBPV = forgetEq U→MultCBPVEq
