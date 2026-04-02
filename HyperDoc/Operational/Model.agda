{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.Model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor

open import HyperDoc.Operational.TransitionSystemAlt

open Category
open Functor

record CBPVModel : Type where 
  field 
    V : Category _ _ 
    C : Category _ _ 
    O : Functor ((V ^op) ×C C) TSysCat
