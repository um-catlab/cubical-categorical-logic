-- A (Unary) CBPVCat is a category displayed over KIND, i.e., the free category 𝓥 → 𝓒
-- U and F types are defined as (op)cartesian lifts of the morphism 𝓥 → 𝓒.
-- A CBPVCat with U/F types is a MultCBPVCat i.e. "multiplicative"

-- A CBPVCatᴰ over C is a cat displayed over ∫ C.

-- A MultCBPVCatⱽ over a CBPVCat C has all (op)cartesian lifts of morphisms over 𝓥 → 𝓒

-- A MultCBPVCatᴰ over a MultCBPVCat has displayed U/F as defined below
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Prop

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.Base
open import Cubical.Categories.Displayed.Instances.Weaken
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration.Displayed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰᴰ ℓᴰᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

CBPVCat : ∀ ℓ ℓ' → Type _
CBPVCat = Categoryᴰ KIND

KINDAssoc : EqPsh.ReprEqAssoc KIND
KINDAssoc _ _ _ _ _ _ =
  Eq.pathToEq (isProp-Prop→Type _ _)

KIND^opAssoc : EqPsh.ReprEqAssoc (KIND ^op)
KIND^opAssoc _ _ _ _ _ _ =
  Eq.pathToEq (isProp-Prop→Type _ _)

module _ (C : CBPVCat ℓ ℓ') where
  private
    module C = Categoryᴰ C

  U-Spec : (B : C.ob[ 𝓒 ]) → Presheafⱽ 𝓥 C ℓ'
  U-Spec B = reindPshᴰNatTrans (yoRec (KIND [-, 𝓒 ]) _) (C [-][-, B ])

  -- N.b.: this implies that C is a fibration because the only other
  -- morphisms in the base are identities
  hasU : Type _
  hasU = Quadrable C {x = 𝓥}{y = 𝓒} _

  -- This is better because KIND is strict category
  hasUEq : Type _
  hasUEq = ∀ (B : C.ob[ 𝓒 ]) → EqPsh.CartesianLift C KINDAssoc
    {x = 𝓥}{y = 𝓒}
    _
    B

  -- this similarly implies that C is an opfibration
  hasF : Type _
  hasF = Quadrable (C ^opᴰ) {x = 𝓒}{y = 𝓥} _

  hasFEq : Type _
  hasFEq = ∀ (A : C.ob[ 𝓥 ]) → EqPsh.CartesianLift (C ^opᴰ) KIND^opAssoc
    {x = 𝓒}{y = 𝓥}
    _
    A

  CBPVCatᴰ : ∀ ℓᴰ ℓᴰ' → Type _
  CBPVCatᴰ = Categoryᴰ (∫C C)

MultCBPVCat : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
MultCBPVCat ℓ ℓ' =
  Σ[ C ∈ CBPVCat ℓ ℓ' ] hasU C × hasF C

MultCBPVCatEq : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
MultCBPVCatEq ℓ ℓ' =
  Σ[ C ∈ CBPVCat ℓ ℓ' ] hasUEq C × hasFEq C

forgetEq : MultCBPVCatEq ℓ ℓ' → MultCBPVCat ℓ ℓ'
forgetEq C .fst = C .fst
forgetEq C .snd .fst B =
  EqCartesianLift→CartesianLift
    KINDAssoc
    (C .fst)
    B
    𝓥
    _
    (C .snd .fst B)
forgetEq C .snd .snd A =
  EqCartesianLift→CartesianLift
    KIND^opAssoc
    (C .fst ^opᴰ)
    A
    𝓒
    _
    (C .snd .snd A)

module _ {C : CBPVCat ℓ ℓ'}(Cᴰ : CBPVCatᴰ C ℓᴰ ℓᴰ') where
  private
    module C = Categoryᴰ C using (ob[_])
    module Cᴰ = Categoryᴰ Cᴰ using (ob[_])

  hasUⱽ : Type _
  hasUⱽ = ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}(f : C [ _ ][ A , B ]) → Quadrable Cᴰ (_ , f)

  hasFⱽ : Type _
  hasFⱽ = ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}(f : C [ _ ][ A , B ]) → Quadrable (Cᴰ ^opᴰᴰ) (_ , f)

  hasUᴰ : hasU C → Type _
  hasUᴰ = Liftsᴰ⁺ⱽ.Quadrableᴰ _ _ Cᴰ {k1 = 𝓥}{k2 = 𝓒} _

  hasFᴰ : hasF C → Type _
  hasFᴰ = Liftsᴰ⁺ⱽ.Quadrableᴰ _ _ (Cᴰ ^opᴰᴰ) {k1 = 𝓒}{k2 = 𝓥} _

  module _ (hasUC : hasU C) where
    hasUⱽ→ᴰ : hasUⱽ → hasUᴰ hasUC
    hasUⱽ→ᴰ Uⱽ =
      Liftsᴰ⁺ⱽ.Quadrableⱽ→ᴰ KIND C Cᴰ _ hasUC (Uⱽ _)

  module _ (hasFC : hasF C) where
    hasFⱽ→ᴰ : hasFⱽ → hasFᴰ hasFC
    hasFⱽ→ᴰ Fⱽ =
      Liftsᴰ⁺ⱽ.Quadrableⱽ→ᴰ (KIND ^op) (C ^opᴰ) (Cᴰ ^opᴰᴰ) _ hasFC (Fⱽ _)

MultCBPVCatⱽ : ∀ (C : CBPVCat ℓ ℓ') ℓᴰ ℓᴰ' → Type (ℓ-suc ((ℓ ⊔ℓ ℓ') ⊔ℓ (ℓᴰ ⊔ℓ ℓᴰ')))
MultCBPVCatⱽ C ℓᴰ ℓᴰ' =
  Σ[ Cᴰ ∈ CBPVCatᴰ C ℓᴰ ℓᴰ' ] hasUⱽ Cᴰ × hasFⱽ Cᴰ

MultCBPVCatᴰ : ∀ (C : MultCBPVCat ℓ ℓ') ℓᴰ ℓᴰ' → Type (ℓ-suc ((ℓ ⊔ℓ ℓ') ⊔ℓ (ℓᴰ ⊔ℓ ℓᴰ')))
MultCBPVCatᴰ C ℓᴰ ℓᴰ' =
  Σ[ Cᴰ ∈ CBPVCatᴰ (C .fst) ℓᴰ ℓᴰ' ]
  hasUᴰ Cᴰ (C .snd .fst)
  × hasFᴰ Cᴰ (C .snd .snd)

MultCBPVCatⱽ→ᴰ : {C : MultCBPVCat ℓ ℓ'}
  → MultCBPVCatⱽ (C .fst) ℓᴰ ℓᴰ'
  → MultCBPVCatᴰ C ℓᴰ ℓᴰ'
MultCBPVCatⱽ→ᴰ Cⱽ .fst = Cⱽ .fst
MultCBPVCatⱽ→ᴰ {C = C} Cⱽ .snd .fst =
  hasUⱽ→ᴰ (Cⱽ .fst) (C .snd .fst) (Cⱽ .snd .fst)
MultCBPVCatⱽ→ᴰ {C = C} Cⱽ .snd .snd =
  hasFⱽ→ᴰ (Cⱽ .fst) (C .snd .snd) (Cⱽ .snd .snd)
