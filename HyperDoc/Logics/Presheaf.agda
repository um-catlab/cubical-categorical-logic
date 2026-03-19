{-# OPTIONS --allow-unsolved-metas --type-in-type #-}
module HyperDoc.Logics.Presheaf where

open import Agda.Builtin.Cubical.Equiv
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation renaming (rec to trec)
open import Cubical.Data.Sum

open import Cubical.Relation.Binary.Preorder
open import Cubical.Relation.Binary.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Logic hiding (⊥)

open import Cubical.Categories.Category hiding (isUnivalent)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone

open import HyperDoc.Connectives.Connectives
open import HyperDoc.Syntax

open BinaryRelation
open Category
open Functor
open PreorderStr
open IsPreorder
open isUnivalent
open isEquiv
open MonFun
open NatTrans


module _ 
  {C : Category _ _ }
  (L : Functor (C ^op) (POSET _ _ ))where

  module L = HDSyntax L


  poset : Presheaf C _ → POSET ℓ-zero ℓ-zero .ob 
  poset P .fst .fst = ( e : ob (Elements _ P) ) → L .F-ob (e .fst) .fst .fst
  poset P .fst .snd ._≤_ f g = ( e : ob (Elements _ P) ) → (e .fst) L.◂ f e ≤ g e
  poset P .fst .snd .isPreorder .is-prop-valued f g = isPropΠ λ x →
      is-prop-valued (isPreorder (L .F-ob (x .fst) .fst .snd)) (f x)
      (g x)
  poset P .fst .snd .isPreorder .is-refl = λ a e → is-refl (isPreorder (L .F-ob (e .fst) .fst .snd)) (a e)
  poset P .fst .snd .isPreorder .is-trans = λ a b c z z₁ e →
      is-trans (isPreorder (L .F-ob (e .fst) .fst .snd)) (a e) (b e)
      (c e) (z e) (z₁ e)
  poset P .snd = {!   !}

  PshL : Functor ((PresheafCategory C _) ^op) (POSET _ _ )
  PshL .F-ob P = poset P
  PshL .F-hom {P}{Q} nt .f f (c , Qc)= f (c , N-ob nt c Qc)
  PshL .F-hom nt .isMon = λ z e → z (e .fst , N-ob nt (e .fst) (e .snd))
  PshL .F-id {P} = eqMon _ _ refl
  PshL .F-seq P Q = eqMon _ _ refl 