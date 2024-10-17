{-

  Conditions under which the Fiber category has limits

-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Fiber.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Path
open import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryL
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Fiber
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Functor
open Categoryᴰ
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D)
  where
  private
    module Fib = Categoryᴰ (Fiber F)

  FibTerminal :
    (termC : Terminal C)
    (termFC : isTerminal D (F ⟅ termC .fst ⟆))
    → LiftedTerminal (Fiber F) (terminalToUniversalElement (_ , termFC))
  FibTerminal termC termFC .UniversalElementᴰ.vertexᴰ =
    (termC .fst) , refl
  FibTerminal termC termFC .UniversalElementᴰ.elementᴰ = _
  FibTerminal termC termFC .UniversalElementᴰ.universalᴰ = isIsoToIsEquiv ({!!} , {!!})
