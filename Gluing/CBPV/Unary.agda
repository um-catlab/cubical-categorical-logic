{-# OPTIONS --prop #-}
module Gluing.CBPV.Unary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Prop

open import Cubical.Data.Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Weaken

open Category
open Section

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open Functorᴰ

-- A CBPV model
module UnaryGluing
  (Ob : Kind → Type ℓ)
  (Fun : ∀ {k1 k2} → ≤Kind k1 k2 → Ob k1 → Ob k2 → Type ℓ')
  (𝟙 : Ob 𝓥)
  where
  VTy = Ob 𝓥
  CTy = Ob 𝓒

  open CBPV Ob Fun

  -- The trivial effects: (weaken KIND (SET (ℓ-max ℓ ℓ')))
  -- Predicates on that: reindex PROPᴰ or SETᴰ to be over that?

  CBPV-SET : Categoryᴰ KIND (ℓ-suc (ℓ-max ℓ ℓ')) (ℓ-max ℓ ℓ')
  CBPV-SET = weaken KIND (SET (ℓ-max ℓ ℓ'))

  -- TODO: make this a general definition?
  closed : Functorⱽ CBPV CBPV-SET
  closed .F-obᴰ Γ = CBPV.Hom[ _ ][ 𝟙 , Γ ] , isSetTm
  closed .F-homᴰ f g = seqS g f
  closed .F-idᴰ i g = IdRS g i
  closed .F-seqᴰ f g i h = AssocS h f g (~ i)

  module FundLem
    (ı-Ob : ∀ {k} → (Γ : Ob k) → Tm tt 𝟙 Γ → hSet ℓᴰ)
    (ı-Fun : ∀ {k1 k2 Γ Δ}{k≤ : ≤Kind k1 k2} (f : Fun k≤ Γ Δ)
      → ∀ (M : Tm tt 𝟙 Γ)
      → ⟨ ı-Ob _ M ⟩ → ⟨ ı-Ob _ (seqS M (gen f)) ⟩ )
    where
    CBPV-SETᴰ : Categoryᴰ (∫C CBPV-SET) (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓᴰ)) (ℓ-max (ℓ-max ℓ ℓ') ℓᴰ)
    CBPV-SETᴰ = EqReindex.reindex (SETᴰ _ ℓᴰ) (weakenΠ KIND (SET (ℓ-max ℓ ℓ'))) Eq.refl (λ _ _ → Eq.refl)

    𝓖 : Categoryᴰ (∫C CBPV) (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓᴰ)) (ℓ-max (ℓ-max ℓ ℓ') ℓᴰ)
    𝓖 = reindex CBPV-SETᴰ (∫F closed)

    fund-lemma : GlobalSection 𝓖
    fund-lemma = Elim.elim 𝓖 ı-Ob (λ {k1} {k2} {Γ} {Δ} {k≤} → ı-Fun)

    corollary : ∀ (M : Tm tt 𝟙 Γ) → ⟨ fund-lemma .F-obᴰ (_ , 𝟙) idS ⟩ → ⟨ ı-Ob _ M ⟩
    corollary M lem = subst (λ M → ⟨ ı-Ob _ M ⟩) (IdLS M) $ fund-lemma .F-homᴰ (_ , M) idS lem

module EZ-Can where
  OB : Kind → Type ℓ-zero
  OB k = Unit

  𝟙 : OB 𝓥
  𝟙 = tt

  Ans : OB 𝓒
  Ans = tt

  FUN : {k1 k2 : Kind} → ≤Kind k1 k2 → OB k1 → OB k2 → Type ℓ-zero
  FUN {𝓥} {𝓥} _ Γ Δ = Empty.⊥
  FUN {𝓥} {𝓒} _ Γ Δ = Bool
  FUN {𝓒} {k2} _ Γ Δ = Empty.⊥

  open CBPV OB FUN

  tru fls : Tm {k1 = 𝓥}{k2 = 𝓒} _ 𝟙 Ans
  tru = gen true
  fls = gen false

  Canonical : ∀ {k}{Γ : OB k} → Tm {k1 = 𝓥}{k2 = k} _ 𝟙 Γ → Type ℓ-zero
  Canonical {𝓥} V = V ≡ idS
  Canonical {𝓒} M = (M ≡ tru) ⊎ (M ≡ fls)

  hCanonical : ∀ {k}{Γ : OB k} → Tm {k1 = 𝓥}{k2 = k} _ 𝟙 Γ → hSet ℓ-zero
  hCanonical M .fst = Canonical M
  hCanonical {𝓥} M .snd = isProp→isSet (isSetTm _ _)
  hCanonical {𝓒} M .snd = isSet⊎ (isProp→isSet (isSetTm _ _)) (isProp→isSet (isSetTm _ _))

  open UnaryGluing.FundLem OB FUN 𝟙 (λ _ → hCanonical)

  -- TODO: cleanup
  AllCanonical : ∀ ((_ , M) : (∫C CBPV) [ (𝓥 , 𝟙) , (𝓒 , Ans) ])
    → Canonical M
  AllCanonical (_ , M) = corollary
    (λ { {𝓥} {𝓒} true M M≡id → inl (cong₂ seqS M≡id refl ∙ IdLS tru)
       ; {𝓥} {𝓒} false M M≡id → inr (cong₂ seqS M≡id refl ∙ IdLS fls)
       })
    M
    refl
