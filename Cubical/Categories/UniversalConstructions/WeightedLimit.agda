{-
  Weighted Limits

  based on the formulation at https://ncatlab.org/nlab/show/weighted+limit
-}
module Cubical.Categories.UniversalConstructions.WeightedLimit where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Functors.More

private
  variable
    ℓC ℓC' ℓK ℓK' ℓS : Level

module _ {C : Category ℓC ℓC'} {K : Category ℓK ℓK'}
  -- the "diagram"
  (c⟨k⟩ : Functor K C)
  -- the "weight"
  -- note that to remove the need for lifts, we would need ℓS = ℓC'
  (W : Functor K (SET ℓS))
  where

  -- c → lim^W_k c⟨k⟩ =~ W → C [ c , c⟨k⟩ ]
  WeightedLimitSpec : Functor (C ^op) (SET _)
  WeightedLimitSpec =
    (FUNCTOR K (SET (ℓ-max ℓC' ℓS)) [ LiftF {ℓS}{ℓC'} ∘F W ,-])
    ∘F λFr _ _ (LiftF {ℓC'}{ℓS} ∘F HomFunctor C ∘F (Id {C = C ^op} ×F c⟨k⟩))
