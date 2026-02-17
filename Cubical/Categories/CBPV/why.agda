{-# OPTIONS --type-in-type #-}
module Cubical.Categories.CBPV.why where 

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal.Instances.Presheaf

open import Cubical.Categories.Category
module experiment {ℓ : Level} (C : Category ℓ ℓ ) where 
  open import Cubical.Categories.Enriched.Instances.Presheaf.Self
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Categories.Monoidal.Enriched
  open EnrichedCategory
  open Iso 
  open PshMon C ℓ 

  𝓒 : Category (ℓ-suc (PshMon.ℓm C ℓ)) (PshMon.ℓm C ℓ) 
  𝓒 = 𝓟

  slf : EnrichedCategory 𝓟Mon ℓ 
  slf = {!  self 𝓒 ? !}
    -- self 𝓒 ℓ

  prf : {P Q : ob slf} → Iso (𝓒 [ 𝟙 , slf .Hom[_,_] P Q ]) (𝓒 [ {! P  !} , {!   !} ]) 
  prf .fun = {!   !}
  prf .inv = {!   !}
  prf .rightInv = {!   !}
  prf .leftInv = {!   !}

module test1 (ℓ : Level) where 
  V = PshMon.𝓟Mon (SET ℓ) ℓ 
  
_ : test1.V ℓ-zero ≡ PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero  
_ = refl -- instantaneous!

module test2 (ℓ : Level) where 
  set = SET ℓ 
  V  = PshMon.𝓟Mon set ℓ 

_ : test2.V  ℓ-zero ≡ PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero 
_ = {!   !} -- takes about 2.5 minutes to check


module pmon (ℓ : Level)(X : Type ℓ) where 
  thing : Type (ℓ-suc ℓ)
  thing = X → Type ℓ

module Test1 (ℓ : Level) where 
  V = pmon.thing (ℓ-suc ℓ) (Type ℓ)

_ : Test1.V ℓ-zero ≡ pmon.thing (ℓ-suc ℓ-zero) (Type ℓ-zero)
_ = refl

module Test2 (ℓ : Level) where 
  set = Type ℓ 
  V = pmon.thing (ℓ-suc ℓ) set

_ : Test2.V ℓ-zero ≡ pmon.thing (ℓ-suc ℓ-zero) (Type ℓ-zero)
_ = refl
   


{-
  annotating set as 
    set : Category (ℓ-suc ℓ) ℓ 
  and annotation V as 
    V : MonoidalCategory (ℓ-suc (PshMon.ℓm set ℓ)) (PshMon.ℓm set ℓ)

  still yield a 2.5+ minute wait


  Note, normalizing the goal in either hole is intantaneous and yields 
  PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero ≡ PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero
-}
