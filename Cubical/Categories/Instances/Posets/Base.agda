{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Posets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category hiding (isUnivalent)
open import Cubical.Data.Unit

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Preorder

open import Cubical.Relation.Binary.Preorder

open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint

private
  variable
    ℓ ℓ' : Level

open Category
open PreorderStr
open isUnivalent

-- Category of Posets
POSET : (ℓ ℓ' : Level) → Category _ _
POSET ℓ ℓ' = record
  { ob = Σ[ P ∈ Preorder ℓ ℓ' ] isUnivalent P
  ; Hom[_,_] = λ X Y → MonFun (X .fst) (Y .fst)
  ; id = MonId
  ; _⋆_ = MonComp
  ; ⋆IdL = λ f → eqMon f f refl
  ; ⋆IdR = λ f → eqMon f f refl
  ; ⋆Assoc = λ f g h → eqMon _ _ refl
  ; isSetHom = λ {_} {Y} → MonFunIsSet (isSetPoset (Y .snd))
  }

-- Displayed Poset for picking out Posets
-- and monotone functions with adjoints
BothAdjᴰ : {ℓ ℓ' : Level} → Preorderᴰ (POSET ℓ ℓ') ℓ-zero _
BothAdjᴰ = record
  { ob[_] = λ x → Unit* {ℓ-zero}
  ; Hom[_][_,_] = λ f x y → HasBothAdj f
  ; idᴰ = IdHasBothAdj
  ; _⋆ᴰ_ = CompHasBothAdj
  ; isPropHomᴰ = λ {x} → isPropHasBothAdj (x .snd) _
  }

-- Category of Posets w/ Both Adjoints
POSETADJ : (ℓ ℓ' : Level) → Category _ _
POSETADJ ℓ ℓ' = ∫C (Preorderᴰ→Catᴰ (BothAdjᴰ {ℓ} {ℓ'}))


-- Displayed Poset for picking out Posets
-- and monotone functions with left adjoints
LeftAdjᴰ : {ℓ ℓ' : Level} → Preorderᴰ (POSET ℓ ℓ') ℓ-zero _
LeftAdjᴰ = record
  { ob[_] = λ x → Unit* {ℓ-zero}
  ; Hom[_][_,_] = λ f x y → HasLeftAdj f
  ; idᴰ = IdHasLeftAdj
  ; _⋆ᴰ_ = CompHasLeftAdj
  ; isPropHomᴰ = λ {x} → isPropHasLeftAdj (x .snd) _
  }

POSETADJL : (ℓ ℓ' : Level) → Category _ _
POSETADJL ℓ ℓ' = ∫C (Preorderᴰ→Catᴰ (LeftAdjᴰ {ℓ} {ℓ'}))

-- Displayed Poset for picking out Posets
-- and monotone functions with right adjoints
RightAdjᴰ : {ℓ ℓ' : Level} → Preorderᴰ (POSET ℓ ℓ') ℓ-zero _
RightAdjᴰ = record
  { ob[_] = λ x → Unit* {ℓ-zero}
  ; Hom[_][_,_] = λ f x y → HasRightAdj f
  ; idᴰ = IdHasRightAdj
  ; _⋆ᴰ_ = CompHasRightAdj
  ; isPropHomᴰ = λ {x} → isPropHasRightAdj (x .snd) _
  }

POSETADJR : (ℓ ℓ' : Level) → Category _ _
POSETADJR ℓ ℓ' = ∫C (Preorderᴰ→Catᴰ (RightAdjᴰ {ℓ} {ℓ'}))
