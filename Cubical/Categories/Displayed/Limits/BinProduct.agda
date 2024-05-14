
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  module D = Categoryᴰ D
  -- TODO: rephrase as displayed universal propery?
  BinProductᴰ : ∀ {c12} → BinProduct' C c12
              → (D.ob[ c12 .fst ] × D.ob[ c12 .snd ])
              → Type _
  BinProductᴰ = RightAdjointAtᴰ (ΔCᴰ D)

  BinProductsᴰ : BinProducts' C → Type _
  BinProductsᴰ = RightAdjointᴰ (ΔCᴰ D)

  FibBinProductsAtᴰ : ∀ {c} → (D.ob[ c ] × D.ob[ c ]) → Type _
  FibBinProductsAtᴰ = LocalRightAdjointAtᴰ (Δᴰ D)

  FibBinProductsᴰ : Type _
  FibBinProductsᴰ = LocalRightAdjointᴰ (Δᴰ D)

--module _ {C : Category ℓC ℓC'} (prod : BinProducts' C) (Cᴰ : Categoryᴰ C ℓD ℓD') where
--  open import Cubical.Categories.Limits.BinProduct.More
--  open import Cubical.Categories.Displayed.BinProduct
--  module PAIR = Categoryᴰ (Cᴰ ×Cᴰ Cᴰ)
--  module Cᴰ = Categoryᴰ Cᴰ
--  open import Cubical.Categories.Displayed.Presheaf
--  open UniversalElementᴰ
--  open import Cubical.Categories.Presheaf
--  open UniversalElement
--  foobar : BinProducts' C → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD')
--  foobar = BinProductsᴰ Cᴰ
--  baz : foobar prod
--  baz = goal
--    where
--    goal : ∀ {d = d} (dᴰ : PAIR.ob[ d ]) → RightAdjointAtᴰ (ΔCᴰ Cᴰ) (prod d) dᴰ
--    goal {d = d} dᴰ .vertexᴰ = abc
--      where
--      abc : Cᴰ.ob[ (prod d) .vertex ]
--      abc = {!!}
--    goal {d = d} dᴰ .elementᴰ = def
--      where
--      def : {!!}
--      def = {!!}
--    goal {d = d} dᴰ .universalᴰ = ghi
--      where
--      ghi : {!!}
--      ghi = {!!}
