{-# OPTIONS --safe #-}
module Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.CartesianCategory.BinaryCartesianCategory
open Category
open BinaryCartesianCategory
open StrictCartesianFunctor

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level
  ℓq ℓq' : Level
  ℓc ℓc' : Level
  ℓd ℓd' : Level

module _ (Vertex : Type ℓ) where
  data ProdTypeExpr : Type ℓ where
    ↑̬ : Vertex → ProdTypeExpr
    _×̬_ : ProdTypeExpr → ProdTypeExpr → ProdTypeExpr
    ⊤̬ : ProdTypeExpr

record ProductQuiver ℓq ℓq' : Type (ℓ-suc (ℓ-max ℓq ℓq')) where
  field
    vertex : Type ℓq
    edge : Type ℓq'
    dom : edge → ProdTypeExpr vertex
    cod : edge → ProdTypeExpr vertex
open ProductQuiver

module _ (Q : ProductQuiver ℓq ℓq')(𝓒 : BinaryCartesianCategory ℓc ℓc') where
  module _ (ı : Q .vertex → 𝓒 .cat .ob) where
    interpret-objects : ProdTypeExpr (Q .vertex) → 𝓒 .cat .ob
    interpret-objects (↑̬ A) = ı A
    interpret-objects (A ×̬ B) = interpret-objects A ×⟨ 𝓒 ⟩ interpret-objects B
    interpret-objects ⊤̬ = 𝓒 .⊤
  
  record Interp : Type (ℓ-max (ℓ-max ℓq ℓq') (ℓ-max ℓc ℓc')) where
    field
      I-ob : Q .vertex → 𝓒 .cat .ob 
      I-hom : (e : Q .edge) → 𝓒 .cat [ interpret-objects I-ob (Q .dom e) , interpret-objects I-ob (Q .cod e) ]
