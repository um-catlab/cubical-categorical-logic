{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.TypeStructure where 
  
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category 

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Lib

open Category

module TypeStructure {Σ : Signature} (M : CBPVModel Σ)  where 
  open CBPVModel M

  HasV𝟙 : Type 
  HasV𝟙  = (A : ob V) → Σ[ X ∈ ob V ] ((V [ A , X ]) ↔ Unit)
  
  HasUTy : Type
  HasUTy = (A : ob V)(B : ob C) → Σ[ X ∈ ob V ] (O'[ A , B ] ↔ (V [ A , X ]))

  HasFTy : Type 
  HasFTy = (A : ob V)(B : ob C) → Σ[ X ∈ ob C ] (O'[ A , B ] ↔ (C [ X , B ]))