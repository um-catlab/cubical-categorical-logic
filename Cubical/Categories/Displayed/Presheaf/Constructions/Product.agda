{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Constructions.Product
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Properties
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.Unit
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Bifunctorᴰ
open Functorᴰ

open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  FinProdPshᴰ :
    {n : ℕ} → {ℓs : Fin n → Level} →
    (Ps : (k : Fin n) → Presheaf C (ℓs k)) →
    {ℓsᴰ : Fin n → Level} →
    ((k : Fin n) → Presheafᴰ (Ps k) Cᴰ (ℓsᴰ k))
    → Presheafᴰ (FinProdPsh Ps) Cᴰ (ℓs-max n ℓsᴰ)
  FinProdPshᴰ {n = zero} Ps Pᴰs = Unit*Pshᴰ
  FinProdPshᴰ {n = suc n} Ps Pᴰs =
    Pᴰs fzero ×ᴰPsh FinProdPshᴰ (λ m → Ps (fsuc m)) (λ m → Pᴰs (fsuc m))

  FinProdPshᴰπ :
    {n : ℕ} {ℓs : Fin n → Level} →
    (Ps : (k : Fin n) → Presheaf C (ℓs k)) →
    {ℓsᴰ : Fin n → Level} →
    (Pᴰs : (k : Fin n) → Presheafᴰ (Ps k) Cᴰ (ℓsᴰ k))
    (k : Fin n) →
    PshHomᴰ (FinProdPshπ Ps k) (FinProdPshᴰ Ps Pᴰs) (Pᴰs k)
  FinProdPshᴰπ {n = suc n} Ps Pᴰs fzero = ×ᴰ-π₁
  FinProdPshᴰπ {n = suc n} Ps Pᴰs (fsuc k) =
    ×ᴰ-π₂
    ⋆PshHomᴰ FinProdPshᴰπ (λ m → Ps (fsuc m)) (λ m → Pᴰs (fsuc m)) k

  FinProdPshᴰ-introᴰ :
    {n : ℕ} {ℓs : Fin n → Level} →
    (Ps : (k : Fin n) → Presheaf C (ℓs k)) →
    {ℓsᴰ : Fin n → Level} →
    (Pᴰs : (k : Fin n) → Presheafᴰ (Ps k) Cᴰ (ℓsᴰ k)) →
    {Q : Presheaf C ℓQ} →
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ} →
    (αs : (k : Fin n) → PshHom Q (Ps k)) →
    (αᴰs : (k : Fin n) → PshHomᴰ (αs k) Qᴰ (Pᴰs k)) →
    PshHomᴰ (FinProdPsh-intro Ps αs) Qᴰ (FinProdPshᴰ Ps Pᴰs)
  FinProdPshᴰ-introᴰ {n = zero} Ps Pᴰs αs αᴰs = Unit*Pshᴰ-introᴰ
  FinProdPshᴰ-introᴰ {n = suc n} Ps Pᴰs αs αᴰs =
    ×ᴰ-introᴰ
      (αᴰs fzero)
      (FinProdPshᴰ-introᴰ
        (λ k → Ps (fsuc k))
        (λ k → Pᴰs (fsuc k))
        (λ k → αs (fsuc k))
        (λ k → αᴰs (fsuc k)))

  FinProdPshᴰ-βᴰ :
    {n : ℕ} {ℓs : Fin n → Level} →
    (Ps : (k : Fin n) → Presheaf C (ℓs k)) →
    {ℓsᴰ : Fin n → Level} →
    (Pᴰs : (k : Fin n) → Presheafᴰ (Ps k) Cᴰ (ℓsᴰ k)) →
    {Q : Presheaf C ℓQ} →
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ} →
    (αs : (k : Fin n) → PshHom Q (Ps k)) →
    (αᴰs : (k : Fin n) → PshHomᴰ (αs k) Qᴰ (Pᴰs k)) →
    (k : Fin n) →
    PshHomᴰPathP
      (FinProdPshᴰ-introᴰ Ps Pᴰs αs αᴰs
         ⋆PshHomᴰ FinProdPshᴰπ Ps Pᴰs k)
       (αᴰs k)
       (FinProdPsh-β Ps αs k)
  FinProdPshᴰ-βᴰ {n = suc n} Ps Pᴰs αs αᴰs fzero =
    ×ᴰPshβ₁ _ _
  FinProdPshᴰ-βᴰ {n = suc n} Ps Pᴰs αs αᴰs (fsuc k) =
    -- TODO replace this with better presheaf
    -- reasoning incoming from Max
    compPshHomᴰPathP'
      (symP (⋆PshHomᴰAssoc _ _ _)) $
      compPshHomᴰPathP (congP₂ (λ _ → _⋆PshHomᴰ_) (×ᴰPshβ₂ _ _) refl) $
      FinProdPshᴰ-βᴰ _ _ _ _ _
