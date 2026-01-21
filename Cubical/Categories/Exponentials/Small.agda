{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Exponentials.Small where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Constructions hiding (π₁; π₂)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C D : Category ℓC ℓC'

open Category

module _ (C : Category ℓC ℓC') where
  Exponential : (c d : C .ob) → (BinProductsWith C c) → Type _
  Exponential c d -×c = UniversalElement C (((C [-, c ]) , -×c) ⇒PshSmall (C [-, d ]))

  Exponentiable : ∀ c → (_×c : BinProductsWith C c) → Type _
  Exponentiable c _×c = ∀ d → Exponential c d _×c

  module _ (bp : BinProducts C) where
    AllExponentiable : Type _
    AllExponentiable = ∀ c → Exponentiable c λ d → bp (d , c)

module ExponentialNotation {C : Category ℓC ℓC'}{c d} -×c (exp : Exponential C c d -×c) where
  private
    module C = Category C
  module ⇒ue = UniversalElementNotation exp
  open ⇒ue
  open BinProductsWithNotation -×c

  vert : C .ob
  vert = vertex

  app : C [ vert ×a , d ]
  app = element

  app' : ∀ {Γ} → C [ Γ , vert ] → C [ Γ , c ] → C [ Γ , d ]
  app' f x = (f ,p x) C.⋆ app

  lda : ∀ {Γ} → C [ Γ ×a , d ] → C [ Γ , vert ]
  lda = intro

module ExponentiableNotation {C : Category ℓC ℓC'}{c}
  -×c
  (c⇒- : Exponentiable C c -×c) where
  -- open BinProductsNotation bp
  c⇒_ : C .ob → C .ob
  c⇒ d = c⇒- d .UniversalElement.vertex

  module _ {c d : C .ob} where
    open ExponentialNotation -×c (c⇒- d) hiding (vert; module ⇒ue) public
  module ⇒ue d = ExponentialNotation.⇒ue -×c (c⇒- d)

module ExponentialsNotation {C : Category ℓC ℓC'} (bp : BinProducts C)
  (exps : AllExponentiable C bp) where
  open BinProductsNotation bp
  _⇒_ : C .ob → C .ob → C .ob
  c ⇒ d = exps c d .UniversalElement.vertex

  module _ {c d : C .ob} where
    open ExponentialNotation (λ d' → bp (d' , c)) (exps c d) hiding (vert; module ⇒ue) public
  module ⇒ue c d = ExponentialNotation.⇒ue (λ d' → bp (d' , c)) (exps c d)
