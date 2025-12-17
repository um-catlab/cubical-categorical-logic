module Cubical.Categories.2Functor.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.2Category.Base
open import Cubical.Categories.2Functor.Base
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Slice.Base
open import Cubical.Categories.Constructions.Slice.Functor
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓC ℓC' ℓC'' ℓD ℓD' ℓD'' : Level

open 2Category
open LaxFunctor
open PseudoFunctor
open GroupoidObjectsCategory
open isUnivalent

module _ {ℓC ℓC'} (C : Category ℓC ℓC') ℓD ℓD' where
  OpFibration : Type _
  OpFibration = PseudoFunctor (Cat→2Cat C) (CAT {ℓC = ℓD} {ℓC' = ℓD'})

module _ {ℓC ℓC'} (C : Category ℓC ℓC') ℓD ℓD' where
  Fibration : Type _
  Fibration = OpFibration (C ^op) ℓD ℓD'

module _ {ℓC ℓC'}
  (C : Category ℓC ℓC') (pb : Pullbacks C)
  {{isUniv : isUnivalent C}}
  where

  open BaseChange pb
  open NatTrans


  CodomainFibration : Fibration C _ _
  CodomainFibration .lax .F₀ c .cat = SliceCat C c
  CodomainFibration .lax .F₀ c .groupoid-obs =
    isGroupoid-ob (preservesUnivalenceSlice C c)
  CodomainFibration .lax .F₁ f = f ＊
  CodomainFibration .lax .F₂ {f = f} {g = g} _ = {!!}
  CodomainFibration .lax .F-id = {!!}
  CodomainFibration .lax .F-seq = {!!}
  CodomainFibration .lax .F-id₂ = {!!}
  CodomainFibration .lax .F-seqⱽ = {!!}
  CodomainFibration .lax .F-seqᴴ = {!!}
  CodomainFibration .lax .F-unitality-l = {!!}
  CodomainFibration .lax .F-unitality-r = {!!}
  CodomainFibration .lax .F-associativity = {!!}
  CodomainFibration .pseudo = {!!}
