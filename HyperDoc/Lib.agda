open import Cubical.Foundations.HLevels
open import Cubical.Data.List
open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category 
open import Cubical.Categories.Functor


open Functor

module HyperDoc.Lib where 

levels : List Level → Level 
levels = foldr ℓ-max ℓ-zero

ℓsuc : List Level → List Level 
ℓsuc = map ℓ-suc

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