{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Preorders.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category

open import Cubical.Relation.Binary.Preorder
open import Cubical.Categories.Instances.Preorders.Monotone

private
  variable
    ℓ ℓ' : Level

open Category

-- Category of Preorders
PREORDER : (ℓ ℓ' : Level) → Category _ _
PREORDER ℓ ℓ' = record
  { ob = Σ[ P ∈ Preorder ℓ ℓ' ] isSet ⟨ P ⟩
  ; Hom[_,_] = λ X Y → MonFun (X .fst) (Y .fst)
  ; id = MonId
  ; _⋆_ = MonComp
  ; ⋆IdL = λ f → eqMon f f refl
  ; ⋆IdR = λ f → eqMon f f refl
  ; ⋆Assoc = λ f g h → eqMon _ _ refl
  ; isSetHom = λ {_} {Y} → MonFunIsSet (Y .snd)
  }
