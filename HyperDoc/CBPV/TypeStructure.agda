{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc
module HyperDoc.CBPV.TypeStructure where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Constructions.Unit

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Lib

open Category

module TypeStructure {Σ : Signature} (M : CBPVModel Σ)  where 
  open CBPVModel M

  HasV𝟙 : Type 
  HasV𝟙 = Representation V UnitPsh

  HasUTy : Type 
  HasUTy = (B : ob C) → Representation V (FORGET ∘F O[-, B ])