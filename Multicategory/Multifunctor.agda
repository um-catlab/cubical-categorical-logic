{-

  Multifunctors of cartesian multicategories.

  The arity is not touched: a multifunctor acts on objects and on
  multimorphisms, leaving the arity type alone, so both laws state
  homogeneously and there is nothing to coerce.

-}
module Multicategory.Multifunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit

open import Multicategory.Cartesian

record Multifunctor
    {ℓI ℓM ℓM' ℓN ℓN' : Level}
    (M : CartesianMulticategory ℓI ℓM ℓM')
    (N : CartesianMulticategory ℓI ℓN ℓN')
    : Type (ℓ-suc (ℓ-max ℓI (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')))) where
  private
    module M = CartesianMulticategory M
    module N = CartesianMulticategory N
  field
    F-ob : M.ob → N.ob
    F-hom : {I : Type ℓI} {Γ : M.Ctx I} {A : M.ob}
      → M.MHom⟨ I ⟩[ Γ , A ] → N.MHom⟨ I ⟩[ (λ i → F-ob (Γ i)) , F-ob A ]

    F-var : {I : Type ℓI} {Γ : M.Ctx I} (i : I)
      → F-hom (M.var {Γ = Γ} i) ≡ N.var i
    F-⋆ : {I J : Type ℓI} {Γ : M.Ctx I} {Δ : M.Ctx J} {A : M.ob}
      (f : M.MHom⟨ I ⟩[ Γ , A ]) (g : (i : I) → M.MHom⟨ J ⟩[ Δ , Γ i ])
      → F-hom (f M.⋆ g) ≡ F-hom f N.⋆ (λ i → F-hom (g i))

open Multifunctor

Idᴹ : ∀ {ℓI ℓM ℓM'} (M : CartesianMulticategory ℓI ℓM ℓM') → Multifunctor M M
Idᴹ M .F-ob A = A
Idᴹ M .F-hom f = f
Idᴹ M .F-var i = refl
Idᴹ M .F-⋆ f g = refl

module _
  {ℓI ℓM ℓM' ℓN ℓN' ℓP ℓP' : Level}
  {M : CartesianMulticategory ℓI ℓM ℓM'}
  {N : CartesianMulticategory ℓI ℓN ℓN'}
  {P : CartesianMulticategory ℓI ℓP ℓP'}
  where
  _∘ᴹ_ : Multifunctor N P → Multifunctor M N → Multifunctor M P
  (G ∘ᴹ F) .F-ob A = G .F-ob (F .F-ob A)
  (G ∘ᴹ F) .F-hom f = G .F-hom (F .F-hom f)
  (G ∘ᴹ F) .F-var i = cong (G .F-hom) (F .F-var i) ∙ G .F-var i
  (G ∘ᴹ F) .F-⋆ f g =
    cong (G .F-hom) (F .F-⋆ f g) ∙ G .F-⋆ (F .F-hom f) (λ i → F .F-hom (g i))

-- the endomorphism clone of a set sits inside SET: on multimorphisms
-- it is the identity, so both laws are refl
Endₘ↪SETₘ : ∀ {ℓI ℓ} (X : hSet ℓ) → Multifunctor (Endₘ {ℓI} X) (SETₘ {ℓI} {ℓ})
Endₘ↪SETₘ X .F-ob _ = X
Endₘ↪SETₘ X .F-hom f = f
Endₘ↪SETₘ X .F-var i = refl
Endₘ↪SETₘ X .F-⋆ f g = refl
