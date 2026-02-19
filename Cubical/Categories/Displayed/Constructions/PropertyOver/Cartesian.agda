{-
  A PropertyOver C P is a CartesianCategoryᴰ when P
  holds at the terminal object and is closed under binary products.

  PropertyOver has contractible homs, so all representability
  proofs are trivial.
  The full UniversalElementᴰ is built from just the vertex data.
-}
module Cubical.Categories.Displayed.Constructions.PropertyOver.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More using (Terminal')
open import Cubical.Categories.Limits.BinProduct.More using (BinProducts)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Unit

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels.PropValuedPresheaf
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Limits.CartesianV'

private
  variable
    ℓC ℓC' ℓP : Level

open UniversalElement
open CartesianCategoryᴰ

module _ (C : Category ℓC ℓC') (P : C .Category.ob → Type ℓP) where
  private Pᴰ = PropertyOver C P

  PropertyOverTerminalᴰ : (term : Terminal' C)
    → P (term .vertex)
    → Terminalᴰ Pᴰ term
  PropertyOverTerminalᴰ term p =
    hasContrHoms+propValuedPshᴰ→UEᴰ Pᴰ (hasContrHomsPropertyOver C P)
      {Pᴰ = UnitPshᴰ {P = UnitPsh}} (λ _ → isPropUnit) term {vᴰ = p} _

  PropertyOverBinProductsᴰ : (bp : BinProducts C)
    → (∀ {A B} → P A → P B → P (bp (A , B) .vertex))
    → BinProductsᴰ Pᴰ bp
  PropertyOverBinProductsᴰ bp p× {A = A} {B = B} pA pB =
    hasContrHoms+propValuedPshᴰ→UEᴰ Pᴰ (hasContrHomsPropertyOver C P)
      {Pᴰ =  _×ᴰPshStrict_ {P = C [-, A ]} {Q = C [-, B ]} (Pᴰ [-][-, pA ]) (Pᴰ [-][-, pB ])}
      (λ _ → isProp× isPropUnit isPropUnit)
      (bp (A , B))
      {vᴰ = p× pA pB}
      _

module _ {CC : CartesianCategory ℓC ℓC'} where
  open CartesianCategory CC

  CartesianPropertyOver : (P : C .Category.ob → Type ℓP)
    → P (term .vertex)
    → (∀ {A B} → P A → P B → P (bp (A , B) .vertex))
    → CartesianCategoryᴰ CC ℓP ℓ-zero
  CartesianPropertyOver P p⊤ p× .Cᴰ = PropertyOver C P
  CartesianPropertyOver P p⊤ p× .termᴰ = PropertyOverTerminalᴰ C P term p⊤
  CartesianPropertyOver P p⊤ p× .bpᴰ = PropertyOverBinProductsᴰ C P bp p×
