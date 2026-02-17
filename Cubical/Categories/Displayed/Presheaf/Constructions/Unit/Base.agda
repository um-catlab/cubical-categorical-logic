module Cubical.Categories.Displayed.Presheaf.Constructions.Unit.Base where

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Functorᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  UnitPshᴰ : ∀ {P : Presheaf C ℓP} → Presheafᴰ P Cᴰ ℓ-zero
  UnitPshᴰ .F-obᴰ _ _ = Unit , isSetUnit
  UnitPshᴰ .F-homᴰ _ _ _ = tt
  UnitPshᴰ .F-idᴰ = refl
  UnitPshᴰ .F-seqᴰ _ _ = refl
