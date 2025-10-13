module Cubical.Categories.Instances.FinCard.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.SumFin
open import Cubical.Data.Nat
open import Cubical.Data.FinSet

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Equivalence.AdjointEquivalence
open import Cubical.Categories.Instances.FinCard.Base
open import Cubical.Categories.Instances.FinSets.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Category
open Functor
open AdjointEquivalence

module _ ℓ where
  FINCARD→FINSET : Functor FINCARD (FINSET ℓ)
  FINCARD→FINSET .F-ob n = mkfs (Lift $ Fin n) (isFinSetLift isFinSetFin)
  FINCARD→FINSET .F-hom f .fst (lift m) = lift (f m)
  FINCARD→FINSET .F-hom f .snd = _
  FINCARD→FINSET .F-id = refl
  FINCARD→FINSET .F-seq _ _ = refl

  FINSET→FINCARD : Functor (FINSET ℓ) FINCARD
  FINSET→FINCARD .F-ob A = card ⟨ A ⟩fs
  FINSET→FINCARD .F-hom {x = A} {y = B} (f , _) m = {!!}
  FINSET→FINCARD .F-id = {!!}
  FINSET→FINCARD .F-seq = {!!}


  FINCARD≅FINSET : AdjointEquivalence FINCARD (FINSET ℓ)
  FINCARD≅FINSET .fun = FINCARD→FINSET
  FINCARD≅FINSET .inv = FINSET→FINCARD
  FINCARD≅FINSET .η = {!!}
  FINCARD≅FINSET .ε = {!!}
  FINCARD≅FINSET .triangleIdentities = {!!}
