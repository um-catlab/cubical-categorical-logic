
module Cubical.Categories.Limits.AsRepresentable where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Bifunctor as Bif
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Adjoint.UniversalElements

open import Cubical.Categories.Profunctor.General

private
  variable
    ℓj ℓj' ℓc ℓc' : Level

ΔCone : {C : Category ℓc ℓc'}{J : Category ℓj ℓj'}
  → Functor C (FUNCTOR J C)
ΔCone = CurryBifunctor Bif.Fst

limitProf : {C : Category ℓc ℓc'}{J : Category ℓj ℓj'}
        → Profunctor (FUNCTOR J C) C (ℓ-max (ℓ-max ℓc' ℓj) ℓj')
limitProf = RightAdjointProf ΔCone

limit : {C : Category ℓc ℓc'}{J : Category ℓj ℓj'}
        (D : Functor J C)
      → Type _
limit {C = C}{J = J} = RightAdjointAt {C = C}{D = FUNCTOR J C}ΔCone

limitsOfShape : (C : Category ℓc ℓc') (J : Category ℓj ℓj')
              → Type _
limitsOfShape C J =
  RightAdjoint {C = C}{D = FUNCTOR J C} ΔCone

limitF : {C : Category ℓc ℓc'}{J : Category ℓj ℓj'}
  → limitsOfShape C J → Functor (FUNCTOR J C) C
limitF {C = C}{J = J} lims =
  FunctorComprehension {C = FUNCTOR J C}{D = C} (RightAdjointProf ΔCone)
    lims

-- TODO: All functors preserve cones
--       Functors with left adjoints preserve limiting cones
