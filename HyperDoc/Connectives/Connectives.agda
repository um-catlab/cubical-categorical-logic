-- TODO for later.. come up with a nice way to make this modular
-- can this be a purely modular construction... 
-- perhaps not when we think about laws ?

module HyperDoc.Connectives.Connectives where

open import Cubical.Data.Sigma hiding (_∧_;_∨_)

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (_∧_;_∨_)
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Relation.Binary.Preorder 
open import Cubical.Categories.Instances.Preorders.Monotone


open Category
open Functor

module L∨⊤ where 

  record HA {ℓ ℓ'} (P : ob (POSET ℓ ℓ')) : Type (ℓ-max ℓ ℓ') where 
    
    X : Type ℓ
    X = P .fst .fst

    open PreorderStr (P .fst .snd) renaming (_≤_ to _⊢_)
    field 
      top : X
      _∨_ : X → X → X 

      top-top : {P : X} → P ⊢ top

      or_intro_l : {P Q : X} →  P ⊢ P ∨ Q
      or_intro_r : {P Q : X} →  Q ⊢ P ∨ Q
      or_elim : {P Q R : X} →  (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R

      
  record HAHom {ℓ ℓ'}{P Q  : ob (POSET ℓ ℓ')}(F : MonFun (P .fst) (Q .fst))(Hx : HA P)(Hy : HA Q) : Type ℓ where 
    module Hx = HA {ℓ} Hx
    module Hy = HA {ℓ} Hy
    X = P .fst .fst
    open MonFun F
    field 
      f-top : f Hx.top ≡ Hy.top
      f-or : (x x' : X) → f (x Hx.∨ x') ≡  (f x) Hy.∨ (f x')

  -- this could be parameterized by structure
  Has∨⊤ :  ∀{ℓC ℓC' ℓP ℓP'}{C : Category ℓC ℓC'} → Functor (C ^op) (POSET ℓP ℓP') → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓP')  
  Has∨⊤ {C = C} F = Σ[ logic ∈ ((c : ob C) → HA (F .F-ob c)) ] ({c c' : ob C}(f : C [ c' , c ]) → HAHom (F .F-hom f) (logic c) (logic c'))


module L∧ where

  record HA {ℓ ℓ'} (P : ob (POSET ℓ ℓ')) : Type (ℓ-max ℓ ℓ') where 
    
    X : Type ℓ
    X = P .fst .fst

    open PreorderStr (P .fst .snd) renaming (_≤_ to _⊢_)
    field 
      _∧_ : X → X → X 

      and-intro : {P Q R : X} → P ⊢ Q → P ⊢ R → P ⊢ (Q ∧ R) 
      and-elim1 : {P Q R : X} → P ⊢ Q ∧ R → P ⊢ Q 
      and-elim2 : {P Q R : X} → P ⊢ Q ∧ R → P ⊢ R

      
  record HAHom {ℓ ℓ'}{P Q  : ob (POSET ℓ ℓ')}(F : MonFun (P .fst) (Q .fst))(Hx : HA P)(Hy : HA Q) : Type ℓ where 
    module Hx = HA {ℓ} Hx
    module Hy = HA {ℓ} Hy
    X = P .fst .fst
    open MonFun F
    field 
      f-and : (x x' : X) → f (x Hx.∧ x') ≡  (f x) Hy.∧ (f x')

  Has∧ :  ∀{ℓC ℓC' ℓP ℓP'}{C : Category ℓC ℓC'} → Functor (C ^op) (POSET ℓP ℓP') → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓP')  
  Has∧ {C = C} F = Σ[ logic ∈ ((c : ob C) → HA (F .F-ob c)) ] ({c c' : ob C}(f : C [ c' , c ]) → HAHom (F .F-hom f) (logic c) (logic c'))
