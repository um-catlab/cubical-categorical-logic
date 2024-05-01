{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Sets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓC ℓC' ℓD ℓD' : Level

open UniversalElementᴰ
open CartesianOver
open Categoryᴰ

AllCartesianOversSETᴰ : AllCartesianOvers (SETᴰ ℓ ℓ')
AllCartesianOversSETᴰ {c = A} {A'} B' f .f*cᴰ' x = B' (f x)
AllCartesianOversSETᴰ {c = A} {A'} B' f .π a b'  = b'
AllCartesianOversSETᴰ {c = A} {A'} B' f .isCartesian {A''} B'' g gfᴰ =
  uniqueExists gfᴰ refl
    (λ gfᴰ' → SETᴰ _ _ .isSetHomᴰ {A''}{A'}{λ x → f (g x)}{B''}{B'} gfᴰ' gfᴰ)
    λ gfᴰ' → sym

isFibrationSet : isFibration (SETᴰ ℓ ℓ')
isFibrationSet dᴰ = CartesianOver→CartesianLift (SETᴰ _ _)
  (AllCartesianOversSETᴰ _ _)

open import Cubical.Categories.Displayed.Fibration.More
open import Cubical.Data.Unit.Base
open import Cubical.Data.Unit.Properties

-- TODO: huhhhhhhhhhhhhhhhhhhhhh
-- This is definitionally equivalent to LocalRightAdjointᴰ ????
hasFiberedTerminalSet : hasFibTerminal (SETᴰ ℓ ℓ' , isFibrationSet)
hasFiberedTerminalSet dᴰ .vertexᴰ _ = Unit* , isSetUnit*
hasFiberedTerminalSet dᴰ .elementᴰ = tt
hasFiberedTerminalSet dᴰ .universalᴰ .equiv-proof _ =
  uniqueExists (λ _ _ → tt*) (isPropUnit tt tt) (λ _ p q → isSetUnit tt tt p q) λ _ _ → funExt λ _ → funExt λ _ → refl

-- TODO: I don't understand why I can't put `refl` here
foobar : ∀ dᴰ → hasFibTerminal (SETᴰ ℓ ℓ' , isFibrationSet) dᴰ ≡ hasFibTerminal' (SETᴰ ℓ ℓ' , isFibrationSet) dᴰ
foobar dᴰ = {!!}

hasFiberedTerminalSet' : hasFibTerminal' (SETᴰ ℓ ℓ' , isFibrationSet)
hasFiberedTerminalSet' dᴰ .vertexᴰ _ = Unit* , isSetUnit*
hasFiberedTerminalSet' dᴰ .elementᴰ = tt
hasFiberedTerminalSet' dᴰ .universalᴰ .equiv-proof _ =
  uniqueExists (λ _ _ → tt*) (isPropUnit tt tt) (λ _ p q → isSetUnit tt tt p q) λ _ _ → funExt λ _ → funExt λ _ → refl

--= total (SETᴰ ℓ ℓ' , isFibrationSet)

-- I'm sure this is already somewhere, but whatever,
-- let's just rewrite a short version
setHasTerm = Terminal' (SET ℓ ℓ')
setHasTerm = ?

--hasFiberedProductsSet : hasFiberedProducts (SET ℓ ℓ')
--hasFiberedProductsSet = ?
