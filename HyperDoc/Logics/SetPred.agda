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

  has⊤ : L⊤.Has⊤ Pred
  has⊤  .fst X = record { top = λ x → ⊤ ; top-top = λ {P} x _ → tt* }
  has⊤  .snd f .L⊤.HAHom.f-top = refl

  has∧ : L∧.Has∧ Pred 
  has∧ .fst X .L∧.HA._∧_ = _∩_ {X}
  has∧ .fst X .L∧.HA.and-intro f g x Px = (f x Px) , (g x Px)
  has∧ .fst X .L∧.HA.and-elim1 f x Px = f x  Px .fst
  has∧ .fst X .L∧.HA.and-elim2 f x Px = f x Px .snd
  has∧ .snd f .L∧.HAHom.f-and _ _ = refl

  has∨ : L∨.Has∨ Pred 
  has∨ .fst X .L∨.HA._∨_ = _∪_ {X}
  has∨ .fst X .L∨.HA.or-intro1 f x x∈P = ∣ _⊎_.inl (f x x∈P) ∣₁ 
  has∨ .fst X .L∨.HA.or-intro2 f x x∈Q = ∣ _⊎_.inr (f x x∈Q) ∣₁ 
  has∨ .fst X .L∨.HA.or-elim {P}{Q}{R} f g x = trec (∈-isProp P x ) λ {(_⊎_.inl x∈Q ) → f x x∈Q
                                                                    ; (_⊎_.inr x∈R) → g x x∈R}                                        
  has∨ .snd f .L∨.HAHom.f-or _ _ = refl

  open import Cubical.HITs.PropositionalTruncation.Base
  open import Cubical.HITs.PropositionalTruncation.Properties
    renaming (rec to hrec ; map to hmap ; map2 to hmap2 ; elim to helim)
  open import Cubical.Categories.Instances.Preorders.Monotone
  open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
  open import Cubical.Relation.Binary.Preorder
  open PreorderStr
  open import Cubical.Foundations.Isomorphism hiding (section ; retract)
  open Iso
  open _⊣_
  open import Cubical.Data.Sigma 
  has∃ : L∃.Has∃ Pred
  has∃ {A} {A'} f .fst .MonFun.f  P a' = ∥ (Σ[ a ∈ ⟨ A ⟩  ]  (f a ≡ a') × ⟨ P a ⟩) ∥ₚ
  has∃ {A} {A'} f .fst .isMon x≤y a' = hmap λ z → z .fst , z .snd .fst , x≤y (z .fst) (z .snd .snd)
  has∃ {A} {A'} f .snd .adjIff .fun prf a Pa = prf (f a) ∣ (a , (refl , Pa)) ∣₁
  has∃ {A} {A'} f .snd .adjIff {P}{Q} .inv prf a' = hrec (Q a' .snd) λ {(a , eqn , Pa) → subst (λ h → h ∈ Q) eqn (prf a  Pa)}
  has∃ {A} {A'} f .snd .adjIff {P}{Q} .sec b = pred  A .fst .snd .is-prop-valued P (Pred .F-hom {A'}{A} f $ Q)  _ _ 
  has∃ {A} {A'} f .snd .adjIff {P}{Q} .ret a = pred  A' .fst .snd .is-prop-valued (λ x → _ , squash₁) Q   _ _


  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.Sigma
  ⊎Distrib : {X Y : hSet ℓS} → Iso (ℙ (⟨ X ⟩ ⊎ ⟨ Y ⟩  )) (ℙ ⟨ X ⟩ ×  ℙ ⟨ Y ⟩)
  ⊎Distrib {X} {Y} .Iso.fun P = (λ z → P (_⊎_.inl z)) , λ z → P (_⊎_.inr z)
  ⊎Distrib {X} {Y} .Iso.inv (P , Q) (_⊎_.inl x) = P x
  ⊎Distrib {X} {Y} .Iso.inv (P , Q) (_⊎_.inr y) = Q y
  ⊎Distrib {X} {Y} .Iso.sec b = ΣPathP (refl , refl)
  ⊎Distrib {X} {Y} .Iso.ret a = funExt λ {(_⊎_.inl x) → refl
                                   ; (_⊎_.inr x) → refl}