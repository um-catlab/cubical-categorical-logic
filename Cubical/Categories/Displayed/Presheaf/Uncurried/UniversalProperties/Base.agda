{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Curry
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

open Category
open Functor
open Functorᴰ
open PshIso
open Iso

module _ {C : Category ℓC ℓC'}(P : Presheaf C ℓP)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module P = PresheafNotation P
  isFibrationPshᴰ' : Presheafᴰ' P Cᴰ ℓPᴰ → Type _
  isFibrationPshᴰ' Pᴰ = ∀ x (p : P.p[ x ]) → Representableⱽ' Cᴰ x (reindPshᴰNatTrans (yoRec P p) Pᴰ)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  isFibration' : Type _
  isFibration' = ∀ {x}(xᴰ : Cᴰ.ob[ x ]) → isFibrationPshᴰ' (C [-, x ]) Cᴰ (Cᴰ [-][-, xᴰ ]')

  Terminalⱽ : ∀ (x : C.ob) → Type _
  Terminalⱽ x = Representableⱽ' Cᴰ x UnitPshᴰ'

  Terminalsⱽ : Type _
  Terminalsⱽ = ∀ x → Terminalⱽ x

  BinProductⱽ : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Type _
  BinProductⱽ {x} xᴰ yᴰ = Representableⱽ' Cᴰ x ((Cᴰ [-][-, xᴰ ]') ×ⱽPsh (Cᴰ [-][-, yᴰ ]'))

  -- TODO: Need I make this a profunctor?
  BinProductsⱽ : Type _
  BinProductsⱽ = ∀ {x} xᴰ yᴰ → BinProductⱽ {x} xᴰ yᴰ

  LargeExponentialⱽ : ∀ {x} → (xᴰ yᴰ : Cᴰ.ob[ x ]) → Type _
  LargeExponentialⱽ {x} xᴰ yᴰ = Representableⱽ' Cᴰ x ((Cᴰ [-][-, xᴰ ]') ⇒ⱽPshLarge (Cᴰ [-][-, yᴰ ]'))

  LargeExponentialsⱽ : Type _
  LargeExponentialsⱽ = ∀ {x} xᴰ yᴰ → LargeExponentialⱽ {x} xᴰ yᴰ

  isCartesianⱽ : Type _
  isCartesianⱽ = isFibration' × Terminalsⱽ × BinProductsⱽ
