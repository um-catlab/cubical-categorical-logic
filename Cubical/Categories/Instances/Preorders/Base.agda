
module Cubical.Categories.Instances.Preorders.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets

open import Cubical.Relation.Binary.Preorder
open import Cubical.Categories.Instances.Preorders.Monotone

private
  variable
    ℓ ℓ' : Level

open Category
open Functor

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

U : Functor (PREORDER ℓ ℓ) (SET ℓ)
U .F-ob (p , pisSet)= ⟨ p ⟩ , pisSet
U .F-hom f = f .MonFun.f
U .F-id = refl
U .F-seq _ _ = refl

record OrderedFunctor : Type (ℓ-suc ℓ) where
  field
    F : Functor (SET ℓ) (SET ℓ)
    ≤ : Functor (SET ℓ) (PREORDER ℓ ℓ)
    commute : F ≡ U ∘F ≤
