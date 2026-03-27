{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.Instances.Free.CBPV.Strong.Base where

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

open import Cubical.Prop as Prop

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Fiber hiding (fiber)
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Reindex.CartesianClosed
open import Cubical.Categories.Displayed.Instances.Reindex.Exponential
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.Instances.Reindex.UniversalQuantifier
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialV->D

private
  variable
    ℓ ℓ' ℓ'' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open Category
open Categoryᴰ
open Functor
open Section
open PshIso
open PshHom
open UniversalElement

data Sort : Type where
  𝓥 𝓥Ctx 𝓒 𝓒Ctx : Sort

-- This is just a diamond. Maybe start making some compositional
-- constructions on posets?
_≤S_ : Sort → Sort → Prop
𝓥Ctx ≤S s' = ⊤
s ≤S 𝓒 = ⊤
𝓥 ≤S 𝓥 = ⊤
𝓥 ≤S 𝓥Ctx = Prop.⊥
𝓥 ≤S 𝓒Ctx = Prop.⊥
𝓒 ≤S 𝓥 = Prop.⊥
𝓒 ≤S 𝓥Ctx = Prop.⊥
𝓒 ≤S 𝓒Ctx = Prop.⊥
𝓒Ctx ≤S 𝓥 = Prop.⊥
𝓒Ctx ≤S 𝓥Ctx = Prop.⊥
𝓒Ctx ≤S 𝓒Ctx = ⊤

variable
  s s' s'' s1 s2 s3 : Sort

≤S-refl : ∀ s → s ≤S s
≤S-refl 𝓥 = tt
≤S-refl 𝓥Ctx = tt
≤S-refl 𝓒 = tt
≤S-refl 𝓒Ctx = tt

≤S-trans : ∀ {s s' s''} → s ≤S s' → s' ≤S s'' → s ≤S s''
≤S-trans {𝓥} {𝓥} {𝓥} x x₁ = tt
≤S-trans {𝓥} {𝓥} {𝓒} x x₁ = tt
≤S-trans {𝓥} {𝓒} {𝓒} x x₁ = tt
≤S-trans {𝓥Ctx} {s'} {s''} x x₁ = tt
≤S-trans {𝓒} {𝓒} {s''} x x₁ = x₁
≤S-trans {𝓒Ctx} {𝓒} {𝓒} x x₁ = tt
≤S-trans {𝓒Ctx} {𝓒Ctx} {s''} x x₁ = x₁

SORT : Category ℓ-zero ℓ-zero
SORT .ob = Sort
SORT .Hom[_,_] s s' = Prop→Type (s ≤S s')
SORT .id = ı (≤S-refl _)
SORT ._⋆_ s≤ s≤' = ı (≤S-trans (s≤ .Prop→Type.pf) (s≤' .Prop→Type.pf))
SORT .⋆IdL = λ _ → refl
SORT .⋆IdR = λ _ → refl
SORT .⋆Assoc = λ _ _ _ → refl
SORT .isSetHom = isProp→isSet isProp-Prop→Type

data VTy : Type ℓ-zero
data CTy : Type ℓ-zero
data VCtx : Type ℓ-zero
data CCtx : Type ℓ-zero

data VTy where
  [Bool] : VTy
  [U] : CTy → VTy
  _[⊗]_ : VTy → VTy → VTy
data CTy where
  [F] : VTy → CTy
  _[→]_ : VTy → CTy → CTy
data VCtx where
  · : VCtx
  _,:_ : VCtx → VTy → VCtx
data CCtx where
  ∙ : CCtx
  ∙: : CTy → CCtx
  _⊘_ : VCtx → CCtx → CCtx

Ob : Sort → Type
Ob 𝓥 = VTy
Ob 𝓥Ctx = VCtx
Ob 𝓒 = CTy
Ob 𝓒Ctx = CCtx

variable
  X X' X'' X''' : Ob s
  Γ Γ' Γ'' Γ1 Γ2 : VCtx
  A A' A'' A1 A2 : VTy
  Δ Δ' Δ'' Δ1 Δ2 : CCtx
  B B' B'' B1 B2 : CTy
  s≤ s≤' s≤'' : s1 ≤S s2

data Tm : (s ≤S s') → Ob s → Ob s' → Type ℓ-zero where
  idS : ∀ {X : Ob s} → Tm (≤S-refl s) X X
  seqS : (x' : Tm s≤ X X') (x'' : Tm s≤' X' X'') → Tm (≤S-trans s≤ s≤') X X''
  IdLS : (x : Tm s≤ X' X) → seqS idS x ≡ x
  IdRS : (x : Tm s≤ X' X) → seqS x idS ≡ x
  IdAssocS : (x' : Tm s≤ X X') (x'' : Tm s≤' X' X'') (x''' : Tm s≤'' X'' X''')
    → seqS (seqS x' x'') x''' ≡ seqS x' (seqS x'' x''')
  isSetTm : isSet (Tm s≤ X X')

  ·I : Tm _ Γ ·
  ·η : ∀ (γ : Tm _ Γ ·) → γ ≡ ·I

  _,=_ : (γ : Tm _ Γ Γ') (M : Tm _ Γ A) → Tm _ Γ (Γ' ,: A)
  wk : Tm _ (Γ ,: A) Γ
  var : Tm _ (Γ ,: A) A
  wkβ : (γ : Tm _ Γ Γ') (M : Tm _ Γ A) → seqS (γ ,= M) wk ≡ γ
  varβ : (γ : Tm _ Γ Γ') (M : Tm _ Γ A) → seqS (γ ,= M) var ≡ M
  ,:η : (γ,M : Tm _ Γ (Γ' ,: A)) → γ,M ≡ (seqS γ,M wk ,= seqS γ,M var)

  -- -- How to axiomatize ⊘? Some variation on actegories?
  -- ⊘wk : Tm _ ((Γ ,: A) ⊘ Δ) (Γ ⊘ Δ)
  -- ⊘Δ : Tm _ ((Γ ,: A) ⊘ Δ) (Γ ⊘ Δ)
  -- _⊘Tm_ :
  --   Tm _ Γ Γ'
  --   → Tm _ Δ Δ'
  --   → Tm _ (Γ ⊘ Δ) (Γ' ⊘ Δ')

  [λ] : Tm _ ((· ,: A) ⊘ Δ) B → Tm _ Δ (A [→] B)
  [app] : Tm _ ((· ,: A) ⊘ ∙: (A [→] B)) B
  -- TODO: βη
  -- [→β] : ∀ (M : Tm _ ((· ,: A) ⊘ Δ) B) → seqS ({!!} ⊘Tm {!!}) [app] ≡ M
