{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.Instances.Free.SCwF.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.More

import Cubical.Data.Equality as Eq
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Unit

open import Cubical.Prop

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Fiber hiding (fiber)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to SORT; Vertex to Sort; l to CTX; r to TY; ≤Vertex to ≤Sort)
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓ ℓ' ℓ'' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open Category
open Categoryᴰ
open Functor
-- open Section
-- open PshIso
-- open PshHom
-- open UniversalElement

data Ctx : Type ℓ-zero
data Ty : Type ℓ-zero

data Ctx where
  ∙ : Ctx
  _,:_ : Ctx → Ty → Ctx

data Ty where
  [Bool] : Ty
  _[⇒]_ : Ty → Ty → Ty

Ob : Sort → Type ℓ-zero
Ob CTX = Ctx
Ob TY = Ty

variable
  s s' s1 s2 : Sort
  s≤ s≤' s≤'' : ≤Sort s s'

  X Y Z Z' : Ob s
  Δ Γ Θ : Ctx
  A B C D : Ty

data Tm : (≤Sort s s') → Ob s → Ob s' → Type ℓ-zero where
  idS : ∀ {X : Ob s} → Tm (≤V-refl s) X X
  seqS : (y : Tm s≤ X Y) (z : Tm s≤' Y Z) → Tm (≤V-trans s≤ s≤') X Z
  IdLS : (x : Tm s≤ Y X) → seqS idS x ≡ x
  IdRS : (x : Tm s≤ Y X) → seqS x idS ≡ x
  IdAssocS : (y : Tm s≤ X Y) (z : Tm s≤' Y Z) (z' : Tm s≤'' Z Z')
    → seqS (seqS y z) z' ≡ seqS y (seqS z z')
  isSetTm : isSet (Tm s≤ X Y)

  ∙I : Tm _ Γ ∙
  ∙η : ∀ (γ : Tm _ Γ ∙) → γ ≡ ∙I

  _,=_ : (γ : Tm _ Δ Γ) (M : Tm _ Δ A) → Tm _ Δ (Γ ,: A)
  wk : Tm _ (Γ ,: A) Γ
  var : Tm _ (Γ ,: A) A
  wkβ : (γ : Tm _ Δ Γ) (M : Tm _ Δ A) → seqS (γ ,= M) wk ≡ γ
  varβ : (γ : Tm _ Δ Γ) (M : Tm _ Δ A) → seqS (γ ,= M) var ≡ M
  ,:η : (γ,M : Tm _ Δ (Γ ,: A)) → γ,M ≡ (seqS γ,M wk ,= seqS γ,M var)

  [λ] : Tm _ (Γ ,: A) B → Tm _ Γ (A [⇒] B)
  [app] : Tm _ ((∙ ,: (A [⇒] B)) ,: A) B
  [⇒β] : ∀ (M : Tm _ (Γ ,: A) B) → seqS ((∙I ,= seqS wk ([λ] M)) ,= var) [app] ≡ M
  [⇒η] : ∀ (M : Tm _ Γ (A [⇒] B)) → M ≡ [λ] (seqS ((∙I ,= seqS wk M) ,= var) [app])

-- The difference with ordinary λ calculus is the presence of a kind of term
--   Tm _ A B
-- We can think of this as a "subtyping"/"coercion"
Subtyping→Tm : Tm _ A B → Tm _ (∙ ,: A) B
Subtyping→Tm ≤ = seqS var ≤

-- If we want, we can impose an additional condition that the
-- following function is an iso/equiv, or we can just keep it this way
-- and say we don't really care.

-- For the above syntax, we should be able to prove that
--   Tm _ A B ≃ (A ≡ B)
-- But in extensions it is convenient to add some, e.g., [π1] : Tm _ (A1 [×] A2) A1

LAMBDA : Categoryᴰ SORT ℓ-zero ℓ-zero
LAMBDA .ob[_] = Ob
LAMBDA .Hom[_][_,_] s≤ = Tm (s≤ .Prop→Type.pf)
LAMBDA .idᴰ = idS
LAMBDA ._⋆ᴰ_ = seqS
LAMBDA .⋆IdLᴰ = IdLS
LAMBDA .⋆IdRᴰ = IdRS
LAMBDA .⋆Assocᴰ = IdAssocS
LAMBDA .isSetHomᴰ = isSetTm

-- TODO: axiomatize ,= and [⇒] as displayed universal properties.
