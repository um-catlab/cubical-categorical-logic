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

InductiveDiscreteCategory : (A : Type ℓ) → isSet A → Category ℓ ℓ
InductiveDiscreteCategory A isSetA .ob = A
InductiveDiscreteCategory A isSetA .Hom[_,_] x y = EqMore.Eq A x y
InductiveDiscreteCategory A isSetA .id = Eq.refl
InductiveDiscreteCategory A isSetA ._⋆_ = Eq._∙_
InductiveDiscreteCategory A isSetA .⋆IdL Eq.refl = refl
InductiveDiscreteCategory A isSetA .⋆IdR Eq.refl = refl
InductiveDiscreteCategory A isSetA .⋆Assoc Eq.refl Eq.refl Eq.refl = refl
InductiveDiscreteCategory A isSetA .isSetHom =
  isProp→isSet (EqMore.isSet→isSetEq isSetA)

InductiveDiscFunc :
  {A : Type ℓ} {isSetA : isSet A} {C : Category ℓC ℓC'} →
  (A → C .ob) → Functor (InductiveDiscreteCategory A isSetA) C
InductiveDiscFunc f .F-ob = f
InductiveDiscFunc f .F-hom Eq.refl = _
InductiveDiscFunc f .F-id = refl
InductiveDiscFunc {C = C} f .F-seq Eq.refl Eq.refl = sym (C .⋆IdL _)
