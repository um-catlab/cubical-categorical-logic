{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Algebra.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Algebra.Signature.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (l to 𝒱; r to 𝒞)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Algebra.Algebra
open import Cubical.Categories.Displayed.Instances.Algebra.DisplayedAlgebra
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Algebra
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Displayed.FromU
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.FromU

private
  variable
    ℓ ℓᴰ ℓO ℓA : Level

open Category
open Functorᴰ

module _ (Sig : Signature ℓO ℓA) (isSetOp : isSet (Signature.Op Sig)) where
  open Signature Sig

  private
    L = AlgebraLevel Sig

  AlgebraCBPVEq : MultCBPVCatEq (ℓ-suc L) L
  AlgebraCBPVEq = U→MultCBPVEq (ALGForget Sig) (ALGFree Sig isSetOp)

  AlgebraCBPV : MultCBPVCat (ℓ-suc L) L
  AlgebraCBPV = forgetEq AlgebraCBPVEq

  ALGForgetᴰ : Functorᴰ (ALGForget Sig) (ALGᴰ Sig L L) (SETᴰ L L)
  ALGForgetᴰ .F-obᴰ Bᴰ = Bᴰ .fst
  ALGForgetᴰ .F-homᴰ fᴰ = fᴰ .fst
  ALGForgetᴰ .F-idᴰ = refl
  ALGForgetᴰ .F-seqᴰ _ _ = refl

  AlgebraCBPVᴰ : CBPVCatᴰ (AlgebraCBPV .fst) (ℓ-suc L) L
  AlgebraCBPVᴰ = U→CBPVᴰ (ALGForget Sig) ALGForgetᴰ

  AlgebraCBPVAlg : AlgebraEnrichment (AlgebraCBPV .fst) Sig
  AlgebraCBPVAlg .fst A B op γ x = B .snd op (λ v → γ v x)
  AlgebraCBPVAlg .snd .fst V B op γ op⟨γ⟩ p =
    λ i x → p i (V x)
  AlgebraCBPVAlg .snd .snd S A op γ op⟨γ⟩ p =
    funExt λ x → S .snd op (λ v → γ v x) (op⟨γ⟩ x)
      (λ i → p i x)

  module _
    (C : CBPVCat ℓ L) (CAlg : AlgebraEnrichment C Sig)
    (P : Fibers.ob[_] C 𝒱)
    where
    private module C = Fibers C

    points : Functorⱽ C (AlgebraCBPV .fst)
    points .F-obᴰ {x = 𝒱} A = C.Hom[ _ ][ P , A ] , C.isSetHomᴰ
    points .F-obᴰ {x = 𝒞} B =
      ((C.Hom[ _ ][ P , B ] , C.isSetHomᴰ) , CAlg .fst P B)
    points .F-homᴰ {x = 𝒱} {y = 𝒱} f M = M C.⋆ᴰ f
    points .F-homᴰ {x = 𝒱} {y = 𝒞} f M = M C.⋆ᴰ f
    points .F-homᴰ {x = 𝒞} {y = 𝒞} f =
      (λ M → M C.⋆ᴰ f) , CAlg .snd .snd f P
    points .F-idᴰ {x = 𝒱} = funExt C.⋆IdRᴰ
    points .F-idᴰ {x = 𝒞} =
      Σ≡Prop (λ _ → isPropΠ4 λ _ _ _ _ → C.isSetHomᴰ _ _)
        (funExt C.⋆IdRᴰ)
    points .F-seqᴰ {x = 𝒱} {y = 𝒱} {z = 𝒱} f g =
      funExt λ M → sym (C.⋆Assocᴰ M f g)
    points .F-seqᴰ {x = 𝒱} {y = 𝒱} {z = 𝒞} f g =
      funExt λ M → sym (C.⋆Assocᴰ M f g)
    points .F-seqᴰ {x = 𝒱} {y = 𝒞} {z = 𝒞} f g =
      funExt λ M → sym (C.⋆Assocᴰ M f g)
    points .F-seqᴰ {x = 𝒞} {y = 𝒞} {z = 𝒞} f g =
      Σ≡Prop (λ _ → isPropΠ4 λ _ _ _ _ → C.isSetHomᴰ _ _)
        (funExt λ M → sym (C.⋆Assocᴰ M f g))

    pointsPreservesAlgebra :
      PreservesAlgebraEnrichment Sig points CAlg AlgebraCBPVAlg
    pointsPreservesAlgebra A B op γ op⟨γ⟩ p =
      funExt λ V → CAlg .snd .fst V B op γ op⟨γ⟩ p

  AlgebraCBPVAlgᴰ : AlgebraEnrichmentᴰ Sig AlgebraCBPVAlg AlgebraCBPVᴰ
  AlgebraCBPVAlgᴰ .fst Aᴰ Bᴰ op γ γᴰ op⟨γ⟩ p x xᴰ =
    Bᴰ .snd op (λ v → γ v x) (λ v → γᴰ v x xᴰ)
      (op⟨γ⟩ x) (λ i → p i x)
  AlgebraCBPVAlgᴰ .snd .fst {V = V} Vᴰ
    op γ γᴰ op⟨γ⟩ p op⟨γᴰ⟩ pᴰ i x xᴰ =
      pᴰ i (V x) (Vᴰ x xᴰ)
  AlgebraCBPVAlgᴰ .snd .snd {S = S} Sᴰ
    op γ γᴰ op⟨γ⟩ p op⟨γᴰ⟩ pᴰ i x xᴰ =
      Sᴰ .snd op (λ v → γ v x) (λ v → γᴰ v x xᴰ)
        (op⟨γ⟩ x) (λ j → p j x)
        (op⟨γᴰ⟩ x xᴰ) (λ j → pᴰ j x xᴰ) i
