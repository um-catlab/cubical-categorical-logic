{-# OPTIONS --lossy-unification #-}
-- A BiCartesianClosedSection is a GlobalSection of a BiCartesianClosedCategoryᴰ
-- that strictly preserves the bicartesian closed structure (terminal objects,
-- binary products, exponentials, initial objects, and binary coproducts
-- on objects).
module Cubical.Categories.Displayed.Limits.BiCartesianClosedSection where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Limits.BiCartesianClosedV
open import Cubical.Categories.Displayed.Limits.CartesianSection
open import Cubical.Categories.Displayed.Limits.CartesianClosedSection
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Section
open UniversalElement

record BiCartesianClosedSection
  {BCCC : BiCartesianClosedCategory ℓC ℓC'}
  (BCCCᴰ : BiCartesianClosedCategoryᴰ BCCC ℓCᴰ ℓCᴰ')
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
  where
  open BiCartesianClosedCategory BCCC
  open BiCartesianClosedCategoryᴰ BCCCᴰ
  field
    cartesianClosedSection : CartesianClosedSection CCCᴰ
  open CartesianClosedSection cartesianClosedSection public
  field
    F-obᴰ-⊥ : section .F-obᴰ (init .vertex) ≡ initᴰ .fst
    F-obᴰ-+ : ∀ A B → section .F-obᴰ (sums (A , B) .vertex)
             ≡ bcpᴰ (section .F-obᴰ A) (section .F-obᴰ B) .fst
