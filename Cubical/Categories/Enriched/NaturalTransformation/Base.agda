module Cubical.Categories.Enriched.NaturalTransformation.Base where
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor
open EnrichedCategory
open Functor

module _
  {ℓV ℓV'  : Level}
  {V : MonoidalCategory ℓV ℓV'}
  {ℓE : Level}
  {ℓD : Level}
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
      E-N-ob : ∀ (c : C.ob) → V.Hom[ V.unit , D.Hom[ F.F₀ c , G.F₀ c ] ]
      E-N-hom :
        ∀ (c c' : C.ob) →
          (V.ρ⁻¹⟨ C.Hom[ c , c' ] ⟩ V.⋆ ((F.F₁ V.⊗ₕ E-N-ob c') V.⋆ D.seq _ _ _))
            ≡
          (V.η⁻¹⟨ C.Hom[ c , c' ] ⟩ V.⋆ (E-N-ob c V.⊗ₕ G.F₁ V.⋆ D.seq _ _ _))

