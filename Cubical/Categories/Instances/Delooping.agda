module Cubical.Categories.Instances.Delooping where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Unit
open import Cubical.Algebra.Monoid.Base
open import Cubical.Categories.Category

open Category

module _ {ℓ} (M : Monoid ℓ) where
  open MonoidStr (M .snd)

  B : Category ℓ-zero ℓ
  B .ob = Unit
  B .Hom[_,_] _ _ = ⟨ M ⟩
  B .id = ε
  B ._⋆_ = _·_
  B .⋆IdL = ·IdL
  B .⋆IdR = ·IdR
  B .⋆Assoc x y z = sym (·Assoc x y z)
  B .isSetHom = is-set
