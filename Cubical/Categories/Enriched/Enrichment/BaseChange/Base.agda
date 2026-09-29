open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor

module Cubical.Categories.Enriched.Enrichment.BaseChange.Base
  {ℓV ℓV' ℓU ℓU' : Level}
  {V : MonoidalCategory ℓV ℓV'} {U : MonoidalCategory ℓU ℓU'}
  (Fl : LaxMonoidalFunctor V U)
   where

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Enriched.Enrichment.Base

open import Cubical.Foundations.Isomorphism
open Iso

private
  module V = MonoidalCategory V
  module U = MonoidalCategory U
  open LaxMonoidalFunctor Fl

open import Cubical.Categories.Enriched.BaseChange.Base Fl hiding (BaseChange)

module _ {ℓC ℓC' : Level} {C : Category ℓC ℓC'}
  -- (v d Weide 2026) calls this "F preserves underlying Categories"
  -- Using Cruttwell's terminology one could say "F's unit monoidal action" is an isomorphism
  (isIsoε̂  : ∀ (x : V.ob) → isIso (ε̂  {x}))
  (ℰC : Enrichment C V) where
  private
    module ℰC = Enrichment ℰC
  open Enrichment

  BaseChange : Enrichment C U
  BaseChange .VE[_,_] x y = F-ob ℰC.VE[ x , y ]
  BaseChange .id = ε̂ ℰC.id
  BaseChange .seq x y z = μ̂ (ℰC.seq x y z)
  BaseChange .⇄-agree {x} {y} = compIso (ℰC.⇄-agree {x} {y})
    (isIsoToIso (isIsoε̂ ℰC.VE[ x , y ]))
  BaseChange .⋆IdL x y =
      lem-411-L ℰC.id V.id (ℰC.seq x x y) (ℰC.⋆IdL x y)
    ∙ cong (λ k → (ε̂ ℰC.id U.⊗ₕ k) U.⋆ μ̂ (ℰC.seq x x y)) F-id
  BaseChange .⋆IdR x y =
      lem-411-R V.id ℰC.id (ℰC.seq x y y) (ℰC.⋆IdR x y)
    ∙ cong (λ k → (k U.⊗ₕ ε̂ ℰC.id) U.⋆ μ̂ (ℰC.seq x y y)) F-id
  BaseChange .⋆Assoc x y z w =
      sym (U.⋆Assoc _ _ _)
    ∙ lem-413 (ℰC.seq x y z) (ℰC.seq y z w) (ℰC.seq x z w) (ℰC.seq x y w)
        (V.⋆Assoc _ _ _ ∙ ℰC.⋆Assoc x y z w)
