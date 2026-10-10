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
open import Cubical.Categories.Instances.TotalCategory
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

-- The strict (Cubical.Data.Equality) identity and associativity laws of
-- the CBPV category induced by U, given the corresponding strict laws
-- for C and V and strict compatibility of U with them in the two
-- mixed-kind cases. These are what the Eq universal-property machinery
-- (EqPsh.UEⱽ→Reprⱽ and Eq.Conversion.CartesianV) consumes. For every
-- forgetful functor to SET in Instances/, all eight hypotheses are
-- Eq.refl.
module _ {C : Category ℓ ℓ'} {V : Category ℓ ℓ'} (U : Functor C V) where
  private
    module C = Category C
    module V = Category V

  module U→CBPVEqLaws
    (C-idL : EqPsh.EqIdL C) (C-idR : EqPsh.EqIdR C)
    (C-assoc : EqPsh.EqAssoc C)
    (V-idL : EqPsh.EqIdL V) (V-idR : EqPsh.EqIdR V)
    (V-assoc : EqPsh.EqAssoc V)
    (U-idR : ∀ {A B} (f : V [ A , U ⟅ B ⟆ ])
      → f V.⋆ U ⟪ C.id ⟫ Eq.≡ f)
    (U-assoc : ∀ {A X Y Z} (f : V [ A , U ⟅ X ⟆ ])
      (g : C [ X , Y ]) (h : C [ Y , Z ])
      → (f V.⋆ U ⟪ g ⟫) V.⋆ U ⟪ h ⟫ Eq.≡ f V.⋆ U ⟪ g C.⋆ h ⟫)
    where
    private
      D = ∫C (U→CBPV U)
      module D = Category D
      module D^op = Category (D ^op)

    idR : EqPsh.EqIdR D
    idR {x = 𝓥 , A} {y = 𝓥 , B} (_ , f) = Eq.ap (λ g → _ , g) (V-idR f)
    idR {x = 𝓥 , A} {y = 𝓒 , B} (_ , f) = Eq.ap (λ g → _ , g) (U-idR f)
    idR {x = 𝓒 , A} {y = 𝓥 , B} ()
    idR {x = 𝓒 , A} {y = 𝓒 , B} (_ , f) = Eq.ap (λ g → _ , g) (C-idR f)

    idR^op : EqPsh.EqIdR (D ^op)
    idR^op {x = 𝓥 , A} {y = 𝓥 , B} (_ , f) = Eq.ap (λ g → _ , g) (V-idL f)
    idR^op {x = 𝓒 , A} {y = 𝓥 , B} (_ , f) = Eq.ap (λ g → _ , g) (V-idL f)
    idR^op {x = 𝓥 , A} {y = 𝓒 , B} ()
    idR^op {x = 𝓒 , A} {y = 𝓒 , B} (_ , f) = Eq.ap (λ g → _ , g) (C-idL f)

    assoc : EqPsh.ReprEqAssoc D
    assoc (𝓥 , A) {c = 𝓥 , W} {c' = 𝓥 , X} {c'' = 𝓥 , Y}
      (_ , f) (_ , g) (_ , p) _ Eq.refl =
      Eq.ap (λ h → _ , h) (Eq.sym (V-assoc f g p))
    assoc (𝓒 , B) {c = 𝓥 , W} {c' = 𝓥 , X} {c'' = 𝓥 , Y}
      (_ , f) (_ , g) (_ , p) _ Eq.refl =
      Eq.ap (λ h → _ , h) (Eq.sym (V-assoc f g p))
    assoc (𝓒 , B) {c = 𝓥 , W} {c' = 𝓥 , X} {c'' = 𝓒 , Y}
      (_ , f) (_ , g) (_ , p) _ Eq.refl =
      Eq.ap (λ h → _ , h) (Eq.sym (V-assoc f g (U ⟪ p ⟫)))
    assoc (𝓒 , B) {c = 𝓥 , W} {c' = 𝓒 , X} {c'' = 𝓒 , Y}
      (_ , f) (_ , g) (_ , p) _ Eq.refl =
      Eq.ap (λ h → _ , h) (Eq.sym (U-assoc f g p))
    assoc (𝓒 , B) {c = 𝓒 , W} {c' = 𝓒 , X} {c'' = 𝓒 , Y}
      (_ , f) (_ , g) (_ , p) _ Eq.refl =
      Eq.ap (λ h → _ , h) (Eq.sym (C-assoc f g p))
    assoc x f g p f⋆g e = Eq.pathToEq
      (sym (D.⋆Assoc f g p) ∙ cong (λ fg → fg D.⋆ p) (Eq.eqToPath e))

    assoc^op : EqPsh.ReprEqAssoc (D ^op)
    assoc^op (𝓥 , A) {c = 𝓥 , W} {c' = 𝓥 , X} {c'' = 𝓥 , Y}
      (_ , f) (_ , g) (_ , p) _ Eq.refl =
      Eq.ap (λ h → _ , h) (V-assoc p g f)
    assoc^op (𝓥 , A) {c = 𝓒 , W} {c' = 𝓥 , X} {c'' = 𝓥 , Y}
      (_ , f) (_ , g) (_ , p) _ Eq.refl =
      Eq.ap (λ h → _ , h) (V-assoc p g f)
    assoc^op (𝓥 , A) {c = 𝓒 , W} {c' = 𝓒 , X} {c'' = 𝓥 , Y}
      (_ , f) (_ , g) (_ , p) _ Eq.refl =
      Eq.ap (λ h → _ , h) (V-assoc p g (U ⟪ f ⟫))
    assoc^op (𝓥 , A) {c = 𝓒 , W} {c' = 𝓒 , X} {c'' = 𝓒 , Y}
      (_ , f) (_ , g) (_ , p) _ Eq.refl =
      Eq.ap (λ h → _ , h) (U-assoc p g f)
    assoc^op (𝓒 , B) {c = 𝓒 , W} {c' = 𝓒 , X} {c'' = 𝓒 , Y}
      (_ , f) (_ , g) (_ , p) _ Eq.refl =
      Eq.ap (λ h → _ , h) (C-assoc p g f)
    assoc^op x f g p f⋆g e = Eq.pathToEq
      (sym (D^op.⋆Assoc f g p)
      ∙ cong (λ fg → fg D^op.⋆ p) (Eq.eqToPath e))
