module Cubical.Categories.Instances.Discrete.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as EqMore

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

private
  variable
    ℓ ℓC ℓC' : Level

open Category
open Functor

EqDiscreteCategory : (A : Type ℓ) → isSet A → Category ℓ ℓ
EqDiscreteCategory A isSetA .ob = A
EqDiscreteCategory A isSetA .Hom[_,_] x y = EqMore.Eq A x y
EqDiscreteCategory A isSetA .id = Eq.refl
EqDiscreteCategory A isSetA ._⋆_ = Eq._∙_
EqDiscreteCategory A isSetA .⋆IdL Eq.refl = refl
EqDiscreteCategory A isSetA .⋆IdR Eq.refl = refl
EqDiscreteCategory A isSetA .⋆Assoc Eq.refl Eq.refl Eq.refl = refl
EqDiscreteCategory A isSetA .isSetHom =
  isProp→isSet (EqMore.isSet→isSetEq isSetA)

EqDiscFunc :
  {A : Type ℓ} {isSetA : isSet A} {C : Category ℓC ℓC'} →
  (A → C .ob) → Functor (EqDiscreteCategory A isSetA) C
EqDiscFunc f .F-ob = f
EqDiscFunc f .F-hom Eq.refl = _
EqDiscFunc f .F-id = refl
EqDiscFunc {C = C} f .F-seq Eq.refl Eq.refl = sym (C .⋆IdL _)
