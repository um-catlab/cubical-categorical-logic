{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.Limits.AsRepresentable.Cone where




-- module _ {ℓj}{ℓj'}{ℓc}{ℓc'}(J : Category ℓj ℓj')(C : Category ℓc ℓc') where
--   -- In point-wise notation
--   -- CONE c D = NatTrans (J -> Set) (Konst c) D
--   CONE : (FUNCTOR J C) *-[ ℓ-max (ℓ-max ℓj ℓj') ℓc' ]-o C
--   CONE = HomFunctor (FUNCTOR J C) ∘F
--          ((_^opF {C = C}{D = FUNCTOR J C}
--            (λF J C (Fst C J))) ×F Id {C = FUNCTOR J C})
