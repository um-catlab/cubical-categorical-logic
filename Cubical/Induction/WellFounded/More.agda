-- Extensions to Cubical.Induction.WellFounded
module Cubical.Induction.WellFounded.More where

open import Cubical.Foundations.Prelude

open import Cubical.Induction.WellFounded

private
  variable
    ℓA ℓW ℓ< : Level

-- Pull a well-founded relation back along a function.
module _ {A : Type ℓA} {W : Type ℓW} (deg : A → W)
         (_<_ : W → W → Type ℓ<) where
  pullback< : A → A → Type ℓ<
  pullback< a a' = deg a < deg a'

  accPullback : ∀ a → Acc _<_ (deg a) → Acc pullback< a
  accPullback a (acc r) = acc (λ a' p → accPullback a' (r (deg a') p))

  wfPullback : WellFounded _<_ → WellFounded pullback<
  wfPullback wf a = accPullback a (wf (deg a))
