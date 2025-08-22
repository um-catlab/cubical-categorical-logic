{- Coherence theorem for free monoidal categories on a set -}
module Cubical.Categories.Constructions.Free.Monoidal.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.List as List hiding ([_]; rec)

open import Cubical.Categories.HLevels
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.NaturalTransformation.More

open import Cubical.Categories.Constructions.Free.Monoidal.Base as FreeMonoidal
  hiding (rec)
open import Cubical.Categories.Constructions.Free.Monoidal.List as LIST

private
  variable
    ℓ ℓQ ℓQ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ (X : hSet ℓ) where
  private
    FX = FreeMonoidalCategory ⟨ X ⟩
    module FX = MonoidalCategory FX
    j : StrongMonoidalFunctor (LIST X) FX
    j = LIST.rec X FX ↑
    module j = StrongMonoidalFunctor j
  coherence : hasPropHoms FX.C
  coherence = hasPropHomsIsoRetract
    FX.C (|LIST| X) (isoRetract .fst) j.F (isoRetract .snd) (isThin|LIST| X)
    where
      isoRetract = mkRetract ⟨ X ⟩ (LIST X) j (λ x → x ∷ [])
        λ x → NatIsoAt FX.ρ (↑ x)
