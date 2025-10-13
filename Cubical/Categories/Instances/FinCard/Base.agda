module Cubical.Categories.Instances.FinCard.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.SumFin
open import Cubical.Data.Nat

open import Cubical.Categories.Category

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Category

FINCARD : Category ℓ-zero ℓ-zero
FINCARD .ob = ℕ
FINCARD .Hom[_,_] m n = Fin m → Fin n
FINCARD .id = λ z → z
FINCARD ._⋆_ = λ f g z₁ → g (f z₁)
FINCARD .⋆IdL _ = refl
FINCARD .⋆IdR _ = refl
FINCARD .⋆Assoc _ _ _ = refl
FINCARD .isSetHom = isSet→ isSetFin
