-- Finite arities, at an arbitrary level.
--
-- `Free.Explicit` pins a theory's arity level to its variable level, so
-- a theory whose operations are indexed by a set at level ℓ needs its
-- arities there too.  `Lift`ing `⊥`/`Unit`/`Bool` would put a `lower` at
-- every use site, so the arities are given directly.
--
-- None of these has definitional η, so an interpretation applied to a
-- selector agrees with the tuple only up to `funExt`; that is what the
-- η-lemmas here are for.
module Cubical.Algebra.Theory.Arity where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓX : Level

data A0 (ℓ : Level) : Type ℓ where

data A1 (ℓ : Level) : Type ℓ where
  u : A1 ℓ

data A2 (ℓ : Level) : Type ℓ where
  l r : A2 ℓ

data A3 (ℓ : Level) : Type ℓ where
  p q s : A3 ℓ

module _ {X : Type ℓX} where

  sel0 : A0 ℓ → X
  sel0 ()

  sel1 : X → A1 ℓ → X
  sel1 x u = x

  sel2 : X → X → A2 ℓ → X
  sel2 x y l = x
  sel2 x y r = y

  sel3 : X → X → X → A3 ℓ → X
  sel3 x y z p = x
  sel3 x y z q = y
  sel3 x y z s = z

  sel0η : (g : A0 ℓ → X) → g ≡ sel0
  sel0η g = funExt (λ ())

  sel1η : (g : A1 ℓ → X) → g ≡ sel1 (g u)
  sel1η g = funExt (λ { u → refl })

  sel2η : (g : A2 ℓ → X) → g ≡ sel2 (g l) (g r)
  sel2η g = funExt (λ { l → refl ; r → refl })

  sel3η : (g : A3 ℓ → X) → g ≡ sel3 (g p) (g q) (g s)
  sel3η g = funExt (λ { p → refl ; q → refl ; s → refl })
