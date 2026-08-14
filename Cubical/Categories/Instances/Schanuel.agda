{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Categories.Instances.Schanuel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Instances.FullSubcategory.More
open import Cubical.Categories.Instances.Injections
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Pullback.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.CCC
open import Cubical.Categories.Presheaf.Representable

open Category
open UniversalElement

[Inj,Set] : ( ℓ : Level) → Category (ℓ-suc ℓ) ℓ
[Inj,Set] ℓ = PresheafCategory (Inj ^op) ℓ

[Inj,Set]-CCC : (ℓ : Level) → CartesianClosedCategory (ℓ-suc ℓ) ℓ
[Inj,Set]-CCC ℓ = 𝓟-CCC (Inj ^op) ℓ

PullbackPreserving : (ℓ : Level) → [Inj,Set] ℓ .ob → Type _
PullbackPreserving ℓ A =
  PreservesPullbacks {C = (Inj ^op) ^op} {D = SET ℓ} A

Schanuel : ( ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Schanuel ℓ = FullSubcategory ([Inj,Set] ℓ)
  (PullbackPreserving ℓ)

module _ (ℓ : Level) where

  private
    module [Inj,Set]CCC = CartesianClosedCategory ([Inj,Set]-CCC ℓ)

  exponential-preservesPullbacks :
    (A B : Schanuel ℓ .ob) →
    PreservesPullbacks ([Inj,Set]CCC.exps (A .fst) (B .fst) .vertex)
  exponential-preservesPullbacks A B = {! !}

  Schanuel-CCC : CartesianClosedCategory (ℓ-suc ℓ) ℓ
  Schanuel-CCC = FullSubCCC
    ([Inj,Set]-CCC ℓ)
    (PullbackPreserving ℓ)
    (PointwiseContr→PreservesPullbacks _
      (λ _ → isOfHLevelLift 0 isContrUnit))
    (λ {A} {B} →
      PointwiseProductPreservesPullbacks A B)
    (λ {A} {B} A-pb B-pb →
      exponential-preservesPullbacks (A , A-pb) (B , B-pb))
