{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Limits.AsRepresentable.Cone where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Categories.Category renaming (isIso to isIsoC)
-- open import Cubical.Categories.Constructions.BinProduct
-- open import Cubical.Categories.Functor.Base
-- open import Cubical.Categories.NaturalTransformation.Base
-- open import Cubical.Categories.NaturalTransformation.Properties
-- open import Cubical.Categories.Instances.Functors
-- open import Cubical.Categories.Functors.HomFunctor
-- open import Cubical.Categories.Functors.Constant
-- open import Cubical.Categories.Presheaf.Representable

-- open import Cubical.Categories.Instances.Functors.More
-- open import Cubical.Categories.Profunctor.General


-- module _ {ℓj}{ℓj'}{ℓc}{ℓc'}(J : Category ℓj ℓj')(C : Category ℓc ℓc') where
--   -- In point-wise notation
--   -- CONE c D = NatTrans (J -> Set) (Konst c) D
--   CONE : (FUNCTOR J C) *-[ ℓ-max (ℓ-max ℓj ℓj') ℓc' ]-o C
--   CONE = HomFunctor (FUNCTOR J C) ∘F
--          ((_^opF {C = C}{D = FUNCTOR J C}
--            (λF J C (Fst C J))) ×F Id {C = FUNCTOR J C})
