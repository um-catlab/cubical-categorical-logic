{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

module _ {C : Category ℓC ℓC'}(P : Presheaf C ℓP)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module P = PresheafNotation P
  CartesianLift : ∀ {x} (p : P.p[ x ])(Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Type _
  CartesianLift p Pᴰ = Representableⱽ Cᴰ _ (reindPshᴰNatTrans (yoRec P p) Pᴰ)

  isFibrationPshᴰ : Presheafᴰ P Cᴰ ℓPᴰ → Type _
  isFibrationPshᴰ Pᴰ = ∀ x (p : P.p[ x ]) → CartesianLift p Pᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  isFibration : Type _
  isFibration = ∀ {x}(xᴰ : Cᴰ.ob[ x ]) → isFibrationPshᴰ (C [-, x ]) Cᴰ (Cᴰ [-][-, xᴰ ])

  Terminalⱽ : ∀ (x : C.ob) → Type _
  Terminalⱽ x = Representableⱽ Cᴰ x UnitPshᴰ

  Terminalsⱽ : Type _
  Terminalsⱽ = ∀ x → Terminalⱽ x

  BinProductⱽ : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Type _
  BinProductⱽ {x} xᴰ yᴰ = Representableⱽ Cᴰ x ((Cᴰ [-][-, xᴰ ]) ×ⱽPsh (Cᴰ [-][-, yᴰ ]))

  -- TODO: Need I make this a profunctor?
  BinProductsⱽ : Type _
  BinProductsⱽ = ∀ {x} xᴰ yᴰ → BinProductⱽ {x} xᴰ yᴰ

  LargeExponentialⱽ : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Type _
  LargeExponentialⱽ {x} xᴰ yᴰ = Representableⱽ Cᴰ x ((Cᴰ [-][-, xᴰ ]) ⇒ⱽPshLarge (Cᴰ [-][-, yᴰ ]))

  LargeExponentialsⱽ : Type _
  LargeExponentialsⱽ = ∀ {x} xᴰ yᴰ → LargeExponentialⱽ {x} xᴰ yᴰ

  isCartesianⱽ : Type _
  isCartesianⱽ = isFibration × Terminalsⱽ × BinProductsⱽ
