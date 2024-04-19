{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Adjoint.More

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

-- package together a displayed category and its cleavage (isFibration)
Fibration : (C : Category ℓC ℓC') (ℓᴰ ℓᴰ' : Level) →
  Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓᴰ ℓᴰ')))
Fibration C ℓᴰ ℓᴰ' = Σ[ Cᴰ ∈ Categoryᴰ C ℓᴰ ℓᴰ' ] isFibration Cᴰ

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (p : Fibration C ℓCᴰ ℓCᴰ')(q : Fibration D ℓDᴰ ℓDᴰ') where
  module _ {F : Functor C D} (Fᴰ : Functorᴰ F (p .fst) (q .fst)) where
    private
      open Category
      open Functorᴰ
      module Cᴰ = Categoryᴰ (p .fst)
    -- whether a 1-cell preserves cartesian morphisms
    isFibered : Type _
    isFibered =
      ∀ {c c' : C .ob} (c'ᴰ : Cᴰ.ob[ c' ]) (f : C [ c , c' ]) →
      (f*c'ᴰ : Cᴰ.ob[ c ])(fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ]) →
        isCartesianOver (p .fst) c'ᴰ f ( f*c'ᴰ , fᴰ ) →
        isCartesianOver (q .fst) (Fᴰ .F-obᴰ c'ᴰ) (F ⟪ f ⟫) (Fᴰ .F-obᴰ f*c'ᴰ , Fᴰ .F-homᴰ fᴰ)

  -- package together a displayed functor and its structure
  -- of preserving cartesian morphisms
  record FiberedFunctor
      : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
      (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') (ℓ-max ℓDᴰ ℓDᴰ'))) where
    field
      base : Functor C D
      over : Functorᴰ base (p .fst) (q .fst)
      preserves-cartesian : isFibered over

  --VerticalFiberedFunctor =

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (p : Fibration C ℓCᴰ ℓCᴰ')(q : Fibration D ℓDᴰ ℓDᴰ')
  (L : FiberedFunctor p q) where

  open FiberedFunctor

  -- Writing something random to push
  --VerticalFiberedRightAdjoint : Type _
  --VerticalFiberedRightAdjoint = Σ[ R ∈ LocalRightAdjointᴰ (L .over) ] isFibered R
