{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Cartesian.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Isomorphism
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level

CartesianCategory : (ℓ ℓ' : Level) → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
CartesianCategory ℓ ℓ' = Σ[ C ∈ Category ℓ ℓ' ] Terminal C × BinProducts C

module CartesianCategoryNotation (CC : CartesianCategory ℓ ℓ') where
  private
    C = CC .fst
  open Category C
  open Notation C (CC .snd .snd) renaming (_×_ to _×bp_)
  open TerminalNotation C (CC .snd .fst)

  unitor-l : ∀ {a} → CatIso C (𝟙 ×bp a) a
  unitor-l .fst = π₂
  unitor-l .snd .isIso.inv = !t ,p id
  unitor-l .snd .isIso.sec = ×β₂
  unitor-l .snd .isIso.ret =
    ,p-natural ∙ cong₂ _,p_ 𝟙η' (⋆IdR _ ∙ sym (⋆IdL _)) ∙ sym ×η
