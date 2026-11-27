-- Discrete category over a type A
-- A must be an h-groupoid for the homs to be sets

module Cubical.Categories.Instances.Discrete.Eq where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq


private
  variable
    ℓ ℓC ℓC' : Level

open Category

-- Discrete category
DiscreteCategory : hGroupoid ℓ → Category ℓ ℓ
DiscreteCategory A .ob = A .fst
DiscreteCategory A .Hom[_,_] a a' = a Eq.≡ a'
DiscreteCategory A .id = Eq.refl
DiscreteCategory A ._⋆_ = Eq._∙_
DiscreteCategory A .⋆IdL f = refl
DiscreteCategory A .⋆IdR Eq.refl = refl
DiscreteCategory A .⋆Assoc Eq.refl g h = refl
DiscreteCategory A .isSetHom {x} {y} = Eq.isGrpd→isGpdEq (A .snd)
