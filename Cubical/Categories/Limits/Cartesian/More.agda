module Cubical.Categories.Limits.Cartesian.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Constructions.Reindex

private
  variable
    ℓ ℓ' : Level

open Category

module _
  (C : Category ℓ ℓ')
  {Γ A B}
  (A×B : BinProduct C (A , B))
  where
  open BinProductNotation A×B
  CorepCartesian-at : preservesUniversalElement {F = C [ Γ ,-]} (preservesBinProdCones (C [ Γ ,-]) A B) A×B
  CorepCartesian-at X = isIsoToIsEquiv
    ((λ f,g x → f,g .fst x ,p f,g .snd x)
    , (λ _ → ≡-× (funExt λ _ → ×β₁) (funExt λ _ → ×β₂))
    , (λ _ → funExt λ _ → ,p≡ refl refl))

module _
  (CC : CartesianCategory ℓ ℓ')
  (base : CC .CartesianCategory.C .ob)
  where
  open CartesianCategory CC

  CorepCartesian : CartesianFunctor CC (SET ℓ')
  CorepCartesian .fst = C [ base ,-]
  CorepCartesian .snd c c' = CorepCartesian-at C (bp (c , c'))
