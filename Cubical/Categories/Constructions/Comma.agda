module Cubical.Categories.Constructions.Comma where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Foundations.Prelude hiding (Square)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Constructions.Graph

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open Category hiding (_∘_)
open Functor

_↓_ : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}{E : Category ℓE ℓE'}
  (F : Functor C E) (G : Functor D E) → Category _ _
_↓_ {C = C}{D = D}{E = E} F G = Graph
  where open Graph {C = C}{D = D} (HomFunctor E ∘F ((F ^opF) ×F G))

