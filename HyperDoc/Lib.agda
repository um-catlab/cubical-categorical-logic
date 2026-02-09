open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.List renaming (map to lmap ; rec to lrec)
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic 
open import Cubical.Foundations.Powerset
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Displayed.Base

open Categoryᴰ
open Functor

module HyperDoc.Lib where 

levels : List Level → Level 
levels = foldr ℓ-max ℓ-zero

ℓsuc : List Level → List Level 
ℓsuc = lmap ℓ-suc

propBind : {ℓ ℓ' : Level} {A : Type ℓ}{B : Type ℓ'} → ∥ A ∥₁ → (A → ∥ B ∥₁) → ∥ B ∥₁ 
propBind M f = rec squash₁ f M

propBind' : {ℓ ℓ' : Level} {A : Type ℓ}{B : Type ℓ'} → ⟨ ∥ A ∥ₚ ⟩ → (A → ⟨ ∥ B ∥ₚ ⟩ ) → ⟨ ∥ B ∥ₚ ⟩
propBind' M f = propBind M f

to^op^op : {ℓ ℓ' : Level}{C : Category ℓ ℓ'}  → Functor C (C ^op ^op) 
to^op^op .F-ob = λ z → z
to^op^op .F-hom = λ z → z
to^op^op .F-id = refl
to^op^op .F-seq _ _ = refl

from^op^op : {ℓ ℓ' : Level}{C : Category ℓ ℓ'} → Functor (C ^op ^op) C 
from^op^op .F-ob = λ z → z
from^op^op .F-hom = λ z → z
from^op^op .F-id = refl
from^op^op .F-seq _ _ = refl

Cᴰ^op^op : {ℓ ℓ' ℓD ℓD' : Level}{C : Category ℓ ℓ'}
  → Categoryᴰ (C ^op ^op) ℓD ℓD'
  → Categoryᴰ C ℓD ℓD'
Cᴰ^op^op Cᴰ .ob[_] = Cᴰ .ob[_]
Cᴰ^op^op Cᴰ .Hom[_][_,_] = Cᴰ .Hom[_][_,_]
Cᴰ^op^op Cᴰ .idᴰ = Cᴰ .idᴰ
Cᴰ^op^op Cᴰ ._⋆ᴰ_ = Cᴰ ._⋆ᴰ_
Cᴰ^op^op Cᴰ .⋆IdLᴰ = Cᴰ .⋆IdLᴰ
Cᴰ^op^op Cᴰ .⋆IdRᴰ = Cᴰ .⋆IdRᴰ
Cᴰ^op^op Cᴰ .⋆Assocᴰ = Cᴰ .⋆Assocᴰ
Cᴰ^op^op Cᴰ .isSetHomᴰ = Cᴰ .isSetHomᴰ


-- will need this again for operational stuff
module _ {ℓS : Level} where 
  data Gen {A B : hSet ℓS}(f : ⟨ A ⟩ → ⟨ B ⟩ → ⟨ B ⟩ )(P : ℙ ⟨ B ⟩) : ⟨ B ⟩ → Type ℓS where
    base  : ∀ (b) → b ∈ P → Gen f P b
    step  : ∀ (a : ⟨ A ⟩)(b : ⟨ B ⟩) → Gen {A}{B} f P b → Gen f P (f a b)


  Gen-rec :
    ∀ {A B : hSet ℓS}{ℓS' : Level} {X : Type ℓS'}{f : ⟨ A ⟩ → ⟨ B ⟩ → ⟨ B ⟩}{P : ℙ ⟨ B ⟩} →
    -- base case
    (baseC : ∀ (b) → b ∈ P → X) →
    -- step case
    (stepC : ∀ (a : ⟨ A ⟩)(b : ⟨ B ⟩) → X → X) →
    ∀ {b} → Gen {A}{B} f P b → X 
  Gen-rec baseC stepC (base b b∈P) = baseC b b∈P
  Gen-rec baseC stepC (step a b x∈Gen) = stepC a b (Gen-rec baseC stepC x∈Gen)

  Gen-elim :
    ∀ {A B : hSet ℓS}
      {f : ⟨ A ⟩ → ⟨ B ⟩ → ⟨ B ⟩}
      {P : ℙ ⟨ B ⟩}
      {ℓS' : Level} 
      (X : ∀ b → Gen{A}{B} f P b → Type ℓS') →

      -- base case
      (baseC :
        ∀ b (p : b ∈ P) →
        X b (base b p)) →

      -- step case
      (stepC :
        ∀ (a : ⟨ A ⟩)(b : ⟨ B ⟩)
          (g : Gen f P b) →
        X b g →
        X (f a b) (step a b g)) →

      ∀ b (g : Gen f P b) → X b g
  Gen-elim X baseC stepC b (base b' b'∈P ) = baseC b' b'∈P
  Gen-elim {f = f} X baseC stepC b (step a b' b'∈Gen) = stepC a b' b'∈Gen  (Gen-elim X baseC stepC b' b'∈Gen)
