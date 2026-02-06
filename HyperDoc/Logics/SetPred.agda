{-# OPTIONS --allow-unsolved-metas #-}
module HyperDoc.Logics.SetPred where

open import Agda.Builtin.Cubical.Equiv
open import Cubical.Relation.Binary.Preorder
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 
open import Cubical.Foundations.Powerset


open import Cubical.Categories.Category hiding (isUnivalent)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone

open BinaryRelation
open Category
open Functor
open PreorderStr
open IsPreorder
open isUnivalent
open isEquiv
open MonFun

module _ 
  {ℓS ℓP ℓP' : Level}
  where

  pred : hSet ℓS → ob (POSET (ℓ-suc ℓS) ℓS )
  pred X .fst .fst = ℙ ⟨ X ⟩
  pred X .fst .snd ._≤_ = _⊆_
  pred X .fst .snd .isPreorder .is-prop-valued = ⊆-isProp
  pred X .fst .snd .isPreorder .is-refl = ⊆-refl
  pred X .fst .snd .isPreorder .is-trans = ⊆-trans
  -- ⊆-antisym  this exists.. just push it through
  pred X .snd .univ P Q .equiv-proof y .fst = {!   !} , {!   !}
  pred X .snd .univ P Q .equiv-proof y .snd = {!   !}

  Pred : Functor (SET ℓS ^op) (POSET (ℓ-suc ℓS) ℓS) 
  Pred .F-ob = pred
  Pred .F-hom {X} f .f P y = P (f y)
  Pred .F-hom f .isMon = λ z x₂ → z (f x₂)
  Pred .F-id = eqMon _ _ refl
  Pred .F-seq _ _ = eqMon _ _ refl