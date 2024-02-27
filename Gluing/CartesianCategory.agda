{-# OPTIONS --safe #-}
module Gluing.CartesianCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Categories.Constructions.Free.CartesianCategory.Base
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Category.Base

data OB : Type ℓ-zero where
  A B C : OB

-- why do we need this?
-- NOTE to self: Zettel #13
isSetOB : isSet OB
isSetOB = Discrete→isSet
  (sectionDiscrete
  (λ { 0 → A ; 1 → B; _ → C })
  (λ { A → 0 ; B → 1 ; C → 2 })
  (λ { A → refl ; B → refl ; C → refl } )
  discreteℕ)

data MOR : Type ℓ-zero where
  f g : MOR

-- sim
isSetMOR : isSet MOR
isSetMOR = Discrete→isSet
  (sectionDiscrete
  (λ { 0 → f ; 1 → g ; _ → g })
  (λ { f → 0 ; g → 1 })
  (λ { f → refl ; g → refl })
  discreteℕ)

interleaved mutual -- not actually mutually recursive
  DOM COD : MOR → ProdExpr OB

  DOM f = ↑ A
  COD f = ↑ B

  DOM g = ↑ A
  COD g = ↑ C

QUIVER : ×Quiver
QUIVER .fst = OB
QUIVER .snd .ProductQuiver.mor = MOR
QUIVER .snd .ProductQuiver.dom = DOM
QUIVER .snd .ProductQuiver.cod = COD

open ×Quiver-Nice QUIVER

FREECC : CartesianCategory _ _
FREECC = FreeCC' QUIVER

-- our goal
private
  open Category
  |FREECC| : Category _ _
  |FREECC| = FREECC .fst
  FREECC-Cart : BinProducts |FREECC|
  FREECC-Cart = FREECC .snd .snd
  open Notation |FREECC| FREECC-Cart
  _ : (↑ₑ f) ,p (↑ₑ g) ⋆⟨ |FREECC| ⟩ Exp.π₁ ≡ (↑ₑ f)
  _ = {!!}
