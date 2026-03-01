{-# OPTIONS --allow-unsolved-metas #-}
module HyperDoc.Logics.SetPred where

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
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone

open import HyperDoc.Connectives.Connectives

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

  -- generalize these to any category with an internal heyting algebra 
  module _ {X : hSet ℓS} where 

    ⊤ₓ : ℙ ⟨ X ⟩ 
    ⊤ₓ _ = ⊤

    ⊥ₓ : ℙ ⟨ X ⟩
    ⊥ₓ _ = ⊥* , λ ()

    _∩_ : ℙ ⟨ X ⟩ → ℙ ⟨ X ⟩ → ℙ ⟨ X ⟩
    _∩_ P Q x = P x ⊓ Q x

    _∪_ : ℙ ⟨ X ⟩ → ℙ ⟨ X ⟩ → ℙ ⟨ X ⟩ 
    _∪_ P Q x = P x ⊔ Q x 

{-}

  has∨⊤ : L∨⊤.Has∨⊤ Pred
  has∨⊤ .fst X .L∨⊤.HA.top = ⊤ₓ {X}
  has∨⊤ .fst X .L∨⊤.HA._∨_ = _∪_ {X}
  has∨⊤ .fst X .L∨⊤.HA.top-top x Px = tt*
  has∨⊤ .fst X .L∨⊤.HA.or_intro_l x Px = ∣ _⊎_.inl Px ∣₁
  has∨⊤ .fst X .L∨⊤.HA.or_intro_r x Qx = ∣ _⊎_.inr Qx ∣₁
  has∨⊤ .fst X .L∨⊤.HA.or_elim {P}{Q}{R} f g  x = trec (R x .snd) λ { (_⊎_.inl Px) → f x Px
                                                                    ; (_⊎_.inr Qx) → g x Qx} 
  has∨⊤ .snd f .L∨⊤.HAHom.f-top = refl
  has∨⊤ .snd f .L∨⊤.HAHom.f-or _ _ = refl
  -}
  has⊤ : L⊤.Has⊤ Pred
  has⊤  .fst X = record { top = λ x → ⊤ ; top-top = λ {P} x _ → tt* }
  has⊤  .snd f .L⊤.HAHom.f-top = refl

  has∧ : L∧.Has∧ Pred 
  has∧ .fst X .L∧.HA._∧_ = _∩_ {X}
  has∧ .fst X .L∧.HA.and-intro f g x Px = (f x Px) , (g x Px)
  has∧ .fst X .L∧.HA.and-elim1 f x Px = f x  Px .fst
  has∧ .fst X .L∧.HA.and-elim2 f x Px = f x Px .snd
  has∧ .snd f .L∧.HAHom.f-and _ _ = refl