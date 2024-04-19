{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Displayed.Fibration.Base

open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Data.Unit
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open FiberedFunctor

-- terminal fibration over C, ie the identity fibration
module _ {C : Category ℓC ℓC'} where
  open CartesianOver

  1/C = Unitᴰ C

  isFib1/C : isFibration 1/C
  isFib1/C _ = CartesianOver→CartesianLift 1/C ue
    where
    ue : CartesianOver 1/C tt _
    ue .f*cᴰ' = tt
    ue .π = tt
    ue .isCartesian _ _ _ = uniqueExists _ (isPropUnit _ _) (λ _ _ _ → isSetUnit _ _ _ _) λ _ _ → isPropUnit _ _

  TerminalFib : Fibration C _ _
  TerminalFib = (1/C , isFib1/C)

  module _ (p : Fibration C ℓCᴰ ℓCᴰ') where
    open Functorᴰ

    !/C : FiberedFunctor p TerminalFib
    !/C .base = Id
    !/C .over .F-obᴰ _ = tt
    !/C .over .F-homᴰ _ = tt
    !/C .over .F-idᴰ = refl
    !/C .over .F-seqᴰ _ _ = refl
    !/C .preserves-cartesian _ _ _ _ _ _ _ _ =
        uniqueExists tt (isPropUnit tt tt) (λ _ p q → isSetUnit tt tt p q) λ _ _ → isPropUnit tt tt

-- fibered terminal objects
-- TODO: show this gives terminal object in each fiber of the displayed category, directly
module _ {C : Category ℓC ℓC'} (p : Fibration C ℓCᴰ ℓCᴰ') where
  -- Jacobs 1.8.8
  -- Hermida 1.4.1
  hasFibTerminal : Type _
  hasFibTerminal = LocalRightAdjointᴰ (!/C p .over)
