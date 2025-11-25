module Cubical.Categories.Enriched.NaturalTransformation.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched

open EnrichedCategory
open Functor

private
  variable
    ℓV ℓV' ℓD ℓE : Level

module _
  {V : MonoidalCategory ℓV ℓV'}
  {C : EnrichedCategory V ℓE}
  {D : EnrichedCategory V ℓD}
  (F G : EnrichedFunctor V C D) where

  private
    module C = EnrichedCategory C
    module D = EnrichedCategory D
    module V = MonoidalCategory V
    module F = EnrichedFunctor F
    module G = EnrichedFunctor G

  record EnrichedNatTrans :
      Type ((ℓ-max (ℓ-max (ℓ-max ℓV ℓV') (ℓ-suc ℓE)) (ℓ-suc ℓD))) where
    field
      E-N-ob : ∀ (c : C.ob) → V.Hom[ V.unit , D.Hom[ F.F-ob c , G.F-ob c ] ]
      E-N-hom :
        ∀ (c c' : C.ob) →
          (V.ρ⁻¹⟨ C.Hom[ c , c' ] ⟩
            V.⋆ ((F.F-hom V.⊗ₕ E-N-ob c') V.⋆ D.seq _ _ _))
            ≡
          (V.η⁻¹⟨ C.Hom[ c , c' ] ⟩
            V.⋆ (E-N-ob c V.⊗ₕ G.F-hom V.⋆ D.seq _ _ _))

