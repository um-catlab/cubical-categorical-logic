{-# OPTIONS --lossy-unification #-}
-- A CartesianClosedSection is a GlobalSection of a CartesianClosedCategoryᴰ
-- that strictly preserves the cartesian closed structure (terminal objects,
-- binary products, and exponentials on objects).
module Cubical.Categories.Displayed.Limits.CartesianClosedSection where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Limits.CartesianSection
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Section
open UniversalElement

record CartesianClosedSection
  {CCC : CartesianClosedCategory ℓC ℓC'}
  (CCCᴰ : CartesianClosedCategoryᴰ CCC ℓCᴰ ℓCᴰ')
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
  where
  open CartesianClosedCategory CCC
  open CartesianClosedCategoryᴰ CCCᴰ
  field
    cartesianSection : CartesianSection CCᴰ
  open CartesianSection cartesianSection public
  field
    F-obᴰ-⇒ : ∀ A B → section .F-obᴰ (exps A B .vertex)
             ≡ expᴰ (section .F-obᴰ A) (section .F-obᴰ B) .fst
