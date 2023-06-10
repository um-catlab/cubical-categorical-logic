{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Posets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Relation.Binary.Poset

open import Cubical.Categories.Instances.Posets.Monotone
open import Cubical.Categories.Instances.Posets.MonotoneAdjoint

private
  variable
    ℓ ℓ' : Level

open Category

-- Category of Posets
POSET : (ℓ ℓ' : Level) → Category _ _
POSET ℓ ℓ' = record
  { ob = Poset ℓ ℓ'
  ; Hom[_,_] = λ X Y → MonFun X Y
  ; id = MonId
  ; _⋆_ = MonComp
  ; ⋆IdL = λ {X} {Y} f → eqMon f f refl
  ; ⋆IdR = λ {X} {Y} f → eqMon f f refl
  ; ⋆Assoc = λ {X} {Y} {Z} {W} f g h → eqMon _ _ refl
  ; isSetHom = MonFunIsSet
  }


-- Category of Posets w/ Adjoints
POSETADJ : (ℓ ℓ' : Level) → Category _ _
POSETADJ ℓ ℓ' = record
  { ob = Poset ℓ ℓ'
  ; Hom[_,_] = λ X Y → MonFunAdj X Y
  ; id = MonIdAdj
  ; _⋆_ = MonCompAdj
  ; ⋆IdL = λ {X} {Y} f → eqMonAdj _ _
         (eqMon _ _ refl) (eqMon _ _ refl) (eqMon _ _ refl)
  ; ⋆IdR = λ {X} {Y} f → eqMonAdj _ _
         (eqMon _ _ refl) (eqMon _ _ refl) (eqMon _ _ refl)
  ; ⋆Assoc = λ {X} {Y} {Z} {W} f g h → eqMonAdj _ _
           (eqMon _ _ refl) (eqMon _ _ refl) (eqMon _ _ refl)
  ; isSetHom = MonFunAdjIsSet
  }
