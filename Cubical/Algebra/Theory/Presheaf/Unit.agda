{-# OPTIONS --lossy-unification #-}
-- Presheaf models over the unit category are exactly SET models.
module Cubical.Algebra.Theory.Presheaf.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.Indiscrete
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Presheaf.Base

private
  variable
    ℓ ℓ' ℓ'' ℓv ℓX : Level

-- The unit category, with *strict* identity and composition
𝟙 : Category ℓ-zero ℓ-zero
𝟙 = Indiscrete Unit

open Functor
open PshAlg
open PshHomStrict

-- The constant presheaf; its restriction maps are literally the identity
ConstPsh : hSet ℓX → Presheaf 𝟙 ℓX
ConstPsh X .F-ob _ = X
ConstPsh X .F-hom _ x = x
ConstPsh X .F-id = refl
ConstPsh X .F-seq _ _ = refl

module _ {σ : AlgTheorySig ℓ ℓ'} (σeq : AlgTheoryEqns σ ℓ'' ℓv) where

  ConstPshAlg : {X : hSet ℓX} → Alg σeq ⟨ X ⟩
    → PshAlg {C = 𝟙} σeq (ConstPsh X)
  ConstPshAlg B .alg _ = B
  ConstPshAlg B .restr _ = idHomo σeq

  ConstMod : Functor (MOD σeq ℓX) (PMOD {C = 𝟙} σeq ℓX)
  ConstMod .F-ob M = ConstPsh (M .fst) , ConstPshAlg (M .snd)
  ConstMod .F-hom ϕ .fst .N-ob _ = ϕ .fst
  ConstMod .F-hom ϕ .fst .N-hom c c' f p' p eq = cong (ϕ .fst) eq
  ConstMod .F-hom ϕ .snd _ = ϕ .snd
  ConstMod .F-id = refl
  ConstMod .F-seq f g = refl

  -- MOD is a *strict* retract of PMOD over the unit category:
  -- evaluating the constant model gives back the model on the nose.
  Ev∘Const : Ev {C = 𝟙} σeq tt ∘F ConstMod ≡ 𝟙⟨ MOD σeq ℓX ⟩
  Ev∘Const = Functor≡ (λ _ → refl) (λ _ → refl)

  -- ConstMod is fully faithful: over the unit category a strict
  -- presheaf morphism is just a function (naturality is a proposition
  -- and holds automatically).
  module _ {M N : Category.ob (MOD σeq ℓX)} where
    ConstModHomIso : Iso (MOD σeq ℓX [ M , N ])
      (PMOD {C = 𝟙} σeq ℓX [ ConstMod .F-ob M , ConstMod .F-ob N ])
    ConstModHomIso .Iso.fun = ConstMod .F-hom
    ConstModHomIso .Iso.inv α = α .fst .N-ob tt , α .snd tt
    ConstModHomIso .Iso.sec α =
      Σ≡Prop (λ _ → isPropΠ λ _ → isPropHomo σeq (str (N .fst)))
        (makePshHomStrictPath refl)
    ConstModHomIso .Iso.ret _ = refl

  isFullyFaithfulConstMod : isFullyFaithful (ConstMod {ℓX = ℓX})
  isFullyFaithfulConstMod M N = isoToIsEquiv ConstModHomIso

  -- ConstMod is essentially surjective: every presheaf model over the
  -- unit category is isomorphic to a constant one.
  module _ (M : Category.ob (PMOD {C = 𝟙} σeq ℓX)) where
    private
      module P = PresheafNotation (M .fst)
      𝟙MOD = PMOD {C = 𝟙} σeq ℓX

    ConstModCounit : 𝟙MOD [ ConstMod .F-ob (Ev {C = 𝟙} σeq tt .F-ob M) , M ]
    ConstModCounit .fst .N-ob c p = p
    ConstModCounit .fst .N-hom c c' f p' p eq = P.⋆IdL p' ∙ eq
    ConstModCounit .snd c = idHomo σeq

    ConstModCounitInv : 𝟙MOD [ M , ConstMod .F-ob (Ev {C = 𝟙} σeq tt .F-ob M) ]
    ConstModCounitInv .fst .N-ob c p = p
    ConstModCounitInv .fst .N-hom c c' f p' p eq = sym (P.⋆IdL p') ∙ eq
    ConstModCounitInv .snd c = idHomo σeq

    isIsoConstModCounit : isIsoC 𝟙MOD ConstModCounit
    isIsoConstModCounit .isIsoC.inv = ConstModCounitInv
    isIsoConstModCounit .isIsoC.sec =
      Σ≡Prop (λ _ → isPropΠ λ _ → isPropHomo σeq (str (M .fst ⟅ tt ⟆)))
        (makePshHomStrictPath refl)
    isIsoConstModCounit .isIsoC.ret =
      Σ≡Prop (λ _ → isPropΠ λ _ → isPropHomo σeq (str (M .fst ⟅ tt ⟆)))
        (makePshHomStrictPath refl)

  isEssentiallySurjConstMod : isEssentiallySurj (ConstMod {ℓX = ℓX})
  isEssentiallySurjConstMod M =
    PT.∣ ( Ev {C = 𝟙} σeq tt .F-ob M
         , (ConstModCounit M , isIsoConstModCounit M) ) ∣₁

  -- Summary: models in presheaves over the unit category are the same
  -- as models in sets.
  ConstModIsWeakEquiv : isWeakEquivalence (ConstMod {ℓX = ℓX})
  ConstModIsWeakEquiv .isWeakEquivalence.fullfaith = isFullyFaithfulConstMod
  ConstModIsWeakEquiv .isWeakEquivalence.esssurj = isEssentiallySurjConstMod
