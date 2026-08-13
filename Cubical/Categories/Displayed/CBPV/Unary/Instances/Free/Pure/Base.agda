-- CBPV syntax as a category displayed over 𝓥 → 𝓒 ala the Fibrational Framework

-- --lossy-unification here is a convenience for Tm to pick the most
-- general implicits automatically
{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.Pure.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Prop

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)
open import Cubical.Categories.Instances.TotalCategory hiding (elim)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Instances.Reindex

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Category
open Categoryᴰ
open Functor
open Section

module CBPV (Ob : Kind → Type ℓ) (Fun : ∀ {k1 k2} → ≤Kind k1 k2 → Ob k1 → Ob k2 → Type ℓ') where
  VTy = Ob 𝓥
  CTy = Ob 𝓒

  -- WARNING: these are public
  variable
    k k' k1 k2 : Kind

  variable
    Δ Γ Θ Ξ : Ob k
    A A' A'' A1 A2 : VTy
    B B' B'' B1 B2 : CTy
    k≤ k≤' k≤'' : ≤Kind k1 k2

  -- CBPV is a free *displayed category*, but since the base category is
  -- *definitionally* thin, the displayed equalities are simply
  -- equalities.
  data Tm : (k≤ : ≤Kind k1 k2) → Ob k1 → Ob k2 → Type (ℓ-max ℓ ℓ') where
    gen : Fun k≤ Γ Δ → Tm k≤ Γ Δ

    idS : ∀ {Γ : Ob k} → Tm (≤V-refl k) Γ Γ
    seqS : (δ : Tm k≤ Γ Δ) (θ : Tm k≤' Δ Θ) → Tm (≤V-trans k≤ k≤') Γ Θ
    IdLS : (γ : Tm k≤ Δ Γ) → seqS idS γ ≡ γ
    IdRS : (γ : Tm k≤ Δ Γ) → seqS γ idS ≡ γ
    AssocS : (δ : Tm k≤ Γ Δ) (θ : Tm k≤' Δ Θ) (ξ : Tm k≤'' Θ Ξ)
      → seqS (seqS δ θ) ξ ≡ seqS δ (seqS θ ξ)
    isSetTm : isSet (Tm k≤ Γ Δ)

  CBPV : Categoryᴰ KIND ℓ (ℓ-max ℓ ℓ')
  CBPV .ob[_] = Ob
  CBPV .Hom[_][_,_] ≤ = Tm (≤ .Prop→Type.pf)
  CBPV .idᴰ = idS
  CBPV ._⋆ᴰ_ = seqS
  CBPV .⋆IdLᴰ = IdLS
  CBPV .⋆IdRᴰ = IdRS
  CBPV .⋆Assocᴰ = AssocS
  CBPV .isSetHomᴰ = isSetTm

  module CBPV = Categoryᴰ CBPV

  module Elim
    (Cᴰ : Categoryᴰ (∫C CBPV) ℓᴰ ℓᴰ')
    where
    private
      module Cᴰ = Categoryᴰ Cᴰ
    module _
      (ı-Ob : ∀ {k} → (Γ : Ob k) → Cᴰ.ob[ _ , Γ ])
      (ı-Fun : ∀ {k1 k2 Γ Δ}{k≤ : ≤Kind k1 k2} (M : Fun k≤ Γ Δ) → Cᴰ.Hom[ ı k≤ , gen M ][ ı-Ob Γ , ı-Ob Δ ])
      where
      elim-F-homᴰ : (M : Tm k≤ Γ Δ) → Cᴰ.Hom[ ı k≤ , M ][ ı-Ob Γ , ı-Ob Δ ]
      elim-F-homᴰ (gen f) = ı-Fun f
      elim-F-homᴰ idS = Cᴰ.idᴰ
      elim-F-homᴰ (seqS M N) = elim-F-homᴰ M Cᴰ.⋆ᴰ elim-F-homᴰ N
      elim-F-homᴰ (IdLS M i) = Cᴰ.⋆IdLᴰ (elim-F-homᴰ M) i
      elim-F-homᴰ (IdRS M i) = Cᴰ.⋆IdRᴰ (elim-F-homᴰ M) i
      elim-F-homᴰ (AssocS L M N i) = Cᴰ.⋆Assocᴰ (elim-F-homᴰ L) (elim-F-homᴰ M) (elim-F-homᴰ N) i
      elim-F-homᴰ (isSetTm M N p q i j) = isSet→isSetDep
        (λ _ → Cᴰ.isSetHomᴰ)
        (elim-F-homᴰ M)
        (elim-F-homᴰ N)
        (cong elim-F-homᴰ p)
        (cong elim-F-homᴰ q)
        (isSetTm M N p q)
        i j

      elim : GlobalSection Cᴰ
      elim .F-obᴰ d = ı-Ob (d .snd)
      elim .F-homᴰ f = elim-F-homᴰ (f .snd)
      elim .F-idᴰ = refl
      elim .F-seqᴰ _ _ = refl

  -- I guess it's not totally necessary for F to be a Functorⱽ but
  -- once we have UMPs it makes sense.
  module LocalElim
    {C : Categoryᴰ KIND ℓC ℓC'}
    (F : Functorⱽ CBPV C)
    (Cᴰ : Categoryᴰ (∫C C) ℓCᴰ ℓCᴰ')
    where
    private
      module Cᴰ = Categoryᴰ Cᴰ

    localElim :
      (ı-ob : {k : Kind} (Γ : Ob k) → Cᴰ.ob[ k , Functorᴰ.F-obᴰ F Γ ])
      (ı-hom : {k1 k2 : Kind} {Γ : Ob k1} {Δ : Ob k2} {k≤ : ≤Kind k1 k2}
        (M : Fun k≤ Γ Δ) →
        Cᴰ.Hom[ _ , Functorᴰ.F-homᴰ F (gen M) ][ ı-ob Γ , ı-ob Δ ])
      → Section (∫F F) Cᴰ
    localElim ı-ob ı-hom =
      GlobalSectionReindex→Section Cᴰ (∫F F) (Elim.elim (reindex Cᴰ (∫F F)) ı-ob ı-hom)
