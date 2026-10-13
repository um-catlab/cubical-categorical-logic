{-# OPTIONS --lossy-unification #-}
-- A CartesianSection is a GlobalSection of a CartesianCategoryᴰ
-- that strictly preserves the cartesian structure (terminal objects
-- and binary products on objects).
module Cubical.Categories.Displayed.Limits.CartesianSection where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' : Level

open Category
open Section
open UniversalElement

record CartesianSection
  {CC : CartesianCategory ℓC ℓC'}
  (CCᴰ : CartesianCategoryᴰ CC ℓCᴰ ℓCᴰ')
  : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
  where
  open CartesianCategory CC
  open CartesianCategoryᴰ CCᴰ
  field
    section : GlobalSection Cᴰ
    -- section maps the terminal vertex to the displayed terminal vertex
    F-obᴰ-⊤ : section .F-obᴰ (term .vertex) ≡ termᴰ .fst
    -- section maps each product vertex to the displayed product vertex
    F-obᴰ-× : ∀ A B → section .F-obᴰ (bp (A , B) .vertex)
             ≡ bpᴰ (section .F-obᴰ A) (section .F-obᴰ B) .fst
