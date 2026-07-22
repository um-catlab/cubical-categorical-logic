-- CBPV syntax as a category displayed over 𝓥 → 𝓒 ala the Fibrational Framework
-- lossy unification is a convenience, see Base.agda
{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.Full where

open import Cubical.Foundations.Prelude

import Cubical.Data.Equality as Eq
open import Cubical.Prop

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)

open import Cubical.Categories.Displayed.Base

private
  variable
    ℓ ℓ' ℓ'' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open Category
open Categoryᴰ
open Functor

data VTy : Type ℓ-zero
data CTy : Type ℓ-zero

data VTy where
  [1] [Bool] : VTy
  [U] : CTy → VTy

data CTy where
  [F] : VTy → CTy
  _[&]_ : CTy → CTy → CTy
  [⊤] : CTy

Ob : Kind → Type ℓ-zero
Ob 𝓥 = VTy
Ob 𝓒 = CTy

variable
  k k' k1 k2 : Kind

variable
  Δ Γ Θ Ξ : Ob k
  A A' A'' A1 A2 : VTy
  B B' B'' B1 B2 : CTy
  k≤ k≤' k≤'' : ≤Kind k1 k2

data Tm : (k≤ : ≤Kind k1 k2) → Ob k1 → Ob k2 → Type ℓ-zero where
  idS : ∀ {Γ : Ob k} → Tm (≤V-refl k) Γ Γ
  seqS : (δ : Tm k≤ Γ Δ) (θ : Tm k≤' Δ Θ) → Tm (≤V-trans k≤ k≤') Γ Θ
  IdLS : (γ : Tm k≤ Δ Γ) → seqS idS γ ≡ γ
  IdRS : (γ : Tm k≤ Δ Γ) → seqS γ idS ≡ γ
  IdAssocS : (δ : Tm k≤ Γ Δ) (θ : Tm k≤' Δ Θ) (ξ : Tm k≤'' Θ Ξ)
    → seqS (seqS δ θ) ξ ≡ seqS δ (seqS θ ξ)
  isSetTm : isSet (Tm k≤ Γ Δ)

  [ret] : Tm _ A ([F] A)
  [bind] : Tm _ A B → Tm _ ([F] A) B
  [Fβ] : (M : Tm _ A B) → seqS [ret] ([bind] M) ≡ M
  [Fη] : (K : Tm _ ([F] A) B) → K ≡ [bind] (seqS [ret] K)

  [force] : Tm _ ([U] B) B
  [thunk] : Tm _ Γ B → Tm {k1 = 𝓥} _ Γ ([U] B)
  [Uβ] : (M : Tm _ A B) → seqS ([thunk] M) [force] ≡ M
  [Uη] : (V : Tm _ Γ ([U] B)) → V ≡ [thunk] (seqS V [force])

  [⊤I] : Tm (≤V-r-⊤ k) Γ [⊤]
  [⊤η] : (M : Tm (≤V-r-⊤ k) Γ [⊤]) → M ≡ [⊤I]

  [&I] : Tm (≤V-r-⊤ k) Γ B1 → Tm (≤V-r-⊤ k) Γ B2 → Tm (≤V-r-⊤ k) Γ (B1 [&] B2)
  [π1] : Tm _ (B1 [&] B2) B1
  [π2] : Tm _ (B1 [&] B2) B2
  [&β1] : ∀ (M1 : Tm (≤V-r-⊤ k) Γ B1) (M2 : Tm (≤V-r-⊤ k) Γ B2)
    → seqS ([&I] M1 M2) [π1] ≡ M1
  [&β2] : ∀ (M1 : Tm (≤V-r-⊤ k) Γ B1) (M2 : Tm (≤V-r-⊤ k) Γ B2)
    → seqS ([&I] M1 M2) [π2] ≡ M2
  [&η] : (M : Tm (≤V-r-⊤ k) Γ (B1 [&] B2)) →
    M ≡ [&I] (seqS M [π1]) (seqS M [π2])

CBPV : Categoryᴰ KIND ℓ-zero ℓ-zero
CBPV .ob[_] = Ob
CBPV .Hom[_][_,_] ≤ = Tm (≤ .Prop→Type.pf)
CBPV .idᴰ = idS
CBPV ._⋆ᴰ_ = seqS
CBPV .⋆IdLᴰ = IdLS
CBPV .⋆IdRᴰ = IdRS
CBPV .⋆Assocᴰ = IdAssocS
CBPV .isSetHomᴰ = isSetTm
