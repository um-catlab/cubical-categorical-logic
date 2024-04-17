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

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

-- terminal fibration over C, ie the identity fibration
module _ {C : Category ℓC ℓC'} where
  open CartesianOver

  1/C = Unitᴰ C

  isFib1/C : isFibration 1/C
  isFib1/C dᴰ = CartesianOver→CartesianLift 1/C ue
    where
    ue : CartesianOver 1/C tt (dᴰ .snd .snd)
    ue .f*cᴰ' = tt
    ue .π = tt
    ue .isCartesian _ _ _ = uniqueExists _ (isPropUnit _ _) (λ _ _ _ → isSetUnit _ _ _ _) λ _ _ → isPropUnit _ _
    --(record { f*cᴰ' = _ ; π = _ ; isCartesian = λ _ _ _ → uniqueExists _ (isPropUnit _ _) (λ _ _ _ → isSetUnit _ _ _ _) λ _ _ → isPropUnit _ _ })
  TerminalFib : Fibration C _ _
  TerminalFib = (1/C , isFib1/C)

-- fibered terminal objects
-- TODO: show this gives terminal object in each fiber of the displayed category, directly
module _ {C : Category ℓC ℓC'} (p : Fibration C ℓCᴰ ℓCᴰ') where
  ---- ! into TerminalFib
  --open import Cubical.Categories.Functor.Base
  --open import Cubical.Categories.Displayed.Functor
  --TerminalFib! : Functorᴰ Id (p .fst) TerminalFib
  --TerminalFib! .Functorᴰ.F-obᴰ = λ _ → tt
  --TerminalFib! .Functorᴰ.F-homᴰ = λ _ → tt
  --TerminalFib! .Functorᴰ.F-idᴰ = refl
  --TerminalFib! .Functorᴰ.F-seqᴰ = λ _ _ → refl
  --x : isFibered TerminalFib!
  --x c'ᴰ f f*c'ᴰ fᴰ isCartOver c''ᴰ g gfᴰ =
  --  uniqueExists tt (isPropUnit tt tt) (λ _ p q → isSetUnit tt tt p q) λ _ _ → isPropUnit tt tt
---- TODO: hasFibTerminal should be interms of isFibration'
  ----isFibration'
  ---- Jacobs 1.8.8
  ---- Hermida 1.4.1
  --hasFibTerminal : Type _
  --hasFibTerminal = LocalRightAdjointᴰ TerminalFib!
