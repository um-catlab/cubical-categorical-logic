{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.SumFin

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Bifunctor

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓD ℓD' ℓP ℓQ ℓS : Level

open Functor
open PshHom
open PshIso


ℓs-max : (n : ℕ) → (Fin n → Level) → Level
ℓs-max zero _ = ℓ-zero
ℓs-max (suc n) ℓs = ℓ-max (ℓs-max n (ℓs ∘ fsuc)) (ℓs fzero)


module _ {C : Category ℓ ℓ'} where
  FinProdPsh : {n : ℕ} → {ℓs : Fin n → Level} →
    ((k : Fin n) → Presheaf C (ℓs k))
    → Presheaf C (ℓs-max n ℓs)
  FinProdPsh {zero} Ps = Unit*Psh
  FinProdPsh {suc n} {ℓs} Ps =
     -- Confused why I can't write Ps ∘ fsuc below
     Ps fzero ×Psh FinProdPsh (λ m → Ps (fsuc m))

  FinProdPshπ :
    {n : ℕ} {ℓs : Fin n → Level} →
    (Ps : (k : Fin n) → Presheaf C (ℓs k)) →
    (k : Fin n) →
    PshHom (FinProdPsh Ps) (Ps k)
  FinProdPshπ {suc n} {ℓs} Ps fzero = π₁ _ _
  FinProdPshπ {suc n} {ℓs} Ps (fsuc k) =
    π₂ _ _ ⋆PshHom FinProdPshπ (λ m → Ps (fsuc m)) k

  FinProdPsh-intro :
    {n : ℕ} {ℓs : Fin n → Level} →
    (Ps : (k : Fin n) → Presheaf C (ℓs k)) →
    {P : Presheaf C ℓA} →
    ((k : Fin n) → PshHom P (Ps k)) →
    PshHom P (FinProdPsh Ps)
  FinProdPsh-intro {n = zero} {ℓs = ℓs} Ps αs = Unit*Psh-intro
  FinProdPsh-intro {n = suc n} {ℓs = ℓs} Ps αs =
    ×PshIntro (αs fzero) (FinProdPsh-intro (λ m → Ps (fsuc m)) (λ k → αs (fsuc k)))

  FinProdPsh-β :
    {n : ℕ} {ℓs : Fin n → Level} →
    (Ps : (k : Fin n) → Presheaf C (ℓs k)) →
    {P : Presheaf C ℓA} →
    (αs : (k : Fin n) → PshHom P (Ps k)) →
    (k : Fin n) →
    FinProdPsh-intro Ps αs ⋆PshHom FinProdPshπ Ps k ≡ αs k
  FinProdPsh-β {n = suc n} Ps αs fzero = ×Pshβ₁ _ _
  FinProdPsh-β {n = suc n} Ps αs (fsuc k) =
    (sym $ ⋆PshHomAssoc _ _ _)
    ∙ cong₂ _⋆PshHom_ (×Pshβ₂ _ _) refl
    ∙ FinProdPsh-β _ _ _
