{- Category with Type-valued Families -}
module Cubical.Categories.CwF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.Types

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Category

CwF : ∀ (ℓc ℓc' ℓf : Level) → Type {!!}
CwF ℓc ℓc' ℓf = Σ[ C ∈ Category ℓc ℓc' ]
  WildFunctor {!!} (TypeCat ℓf)
