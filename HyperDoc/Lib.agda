open import Cubical.Foundations.HLevels
open import Cubical.Data.List renaming (map to lmap ; rec to lrec)
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic 
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