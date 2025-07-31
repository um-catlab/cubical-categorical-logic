{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Hyperdoctrine.Unary where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Limits.BinProduct.More

private
  variable
    ℓ ℓ' : Level

open Category

record Hyperdoctrine ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    cc : Category ℓ ℓ'
    bp : BinProducts cc
    func : Functor (cc  ^op) (POSETADJ ℓ ℓ')

  open BinProductsNotation bp
  open HasBothAdj

  field
    {-
    Beck-Chevalley condition
    Expresses the naturality of the left/right adjoints of the a × _ projection:
    For f ∈ cc [b , c], we have the following commuting square:

                              func(π₂)
                 func(a × c) ⟵--------- func(c)
                   |         ---------→   |
      func(1 × f)  |         left-adj     | func(f)
                   |                      |
                   ↓          func(π₂)    ↓
                 func(a × b) ←--------- func(b)
                             ---------→
                             left-adj

    -}
    nat-left : ∀ {b c : cc .ob}
      (a : cc .ob) (f : cc [ b , c ]) →
      ((MonComp
        ((func ⟪ (cc .id) ×p f ⟫) .fst)
        ((func ⟪ π₂ {a} {b} ⟫) .snd .left-adj .fst))
      ≡
      (MonComp
        ((func ⟪ π₂ {a} {c} ⟫) .snd .left-adj .fst)
        ((func ⟪ f ⟫) .fst))
      )

    nat-right : ∀ {b c : cc .ob}
      (a : cc .ob) (f : cc [ b , c ]) →
      ((MonComp
        ((func ⟪ (cc .id) ×p f ⟫) .fst)
        ((func ⟪ π₂ {a} {b} ⟫) .snd .right-adj .fst))
      ≡
      (MonComp
        ((func ⟪ π₂ {a} {c} ⟫) .snd .right-adj .fst)
        ((func ⟪ f ⟫) .fst))
      )
