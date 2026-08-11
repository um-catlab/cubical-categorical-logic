-- The co-Eilenberg–Moore comparison functor of an adjunction L ⊣ R,
-- obtained as the Eilenberg–Moore comparison of the opposite
-- adjunction.
module Cubical.Categories.Displayed.Instances.CoEilenbergMoore.Comparison where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Monad

open import Cubical.Categories.Displayed.Instances.CoEilenbergMoore
open import Cubical.Categories.Displayed.Instances.EilenbergMoore.Comparison

private
  variable ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (L : Functor C D) (R : Functor D C) (adj : UnitCounit._⊣_ L R) where

  open UnitCounit

  -- The comonad L ∘F R on D induced by the adjunction
  adjComonad : Comonad D
  adjComonad = (L ^opF) ∘F (R ^opF)
    , MonadFromAdjunction (R ^opF) (L ^opF) (opositeAdjunction adj)

  ComparisonCoEM : Functor C (coEM adjComonad)
  ComparisonCoEM =
    (ComparisonEM (R ^opF) (L ^opF) (opositeAdjunction adj) ^opF) ∘F toOpOp
