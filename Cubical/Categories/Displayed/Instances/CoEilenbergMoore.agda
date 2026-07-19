-- The co-Eilenberg–Moore category of a comonad.
--
-- A comonad on C is a monad on C ^op, so the co-EM category is (the
-- opposite of) the Eilenberg–Moore category of that monad, and
-- everything is inherited from
-- `Cubical.Categories.Displayed.Instances.EilenbergMoore`.
--
-- Note that `Cubical.Categories.Comonad.Base` instead packages a
-- comonad on C as an endofunctor on C with counit and comultiplication;
-- files needing both notions must import qualified.
module Cubical.Categories.Displayed.Instances.CoEilenbergMoore where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Monad.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebras
open import Cubical.Categories.Displayed.Instances.EilenbergMoore
open import Cubical.Categories.Instances.TotalCategory

private
  variable ℓC ℓC' : Level

-- A comonad on C is a monad on the opposite category
Comonad : Category ℓC ℓC' → Type _
Comonad C = Monad (C ^op)

module _ {C : Category ℓC ℓC'} (W : Comonad C) where

  -- Algebras of the monad on C ^op are coalgebras of the underlying
  -- endofunctor on C, and the monad algebra laws are the comonad
  -- coalgebra laws
  coEMᴰ : Categoryᴰ (∫C (ALGᴰ (fst W))) ℓC' ℓ-zero
  coEMᴰ = EMᴰ W

  coEM : Category (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
  coEM = (EM W) ^op

-- A morphism of comonad coalgebras is determined by the carrier map
module _ {C : Category ℓC ℓC'} {W : Comonad C} where

  coEMHom≡ : {X Y : Category.ob (coEM W)}
    {f g : coEM W [ X , Y ]}
    → f .fst .fst ≡ g .fst .fst → f ≡ g
  coEMHom≡ {X} {Y} = emHom≡ {Mon = W} {X = Y} {Y = X}
