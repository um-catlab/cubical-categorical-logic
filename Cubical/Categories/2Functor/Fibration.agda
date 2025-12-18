module Cubical.Categories.2Functor.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.2Category.Base
open import Cubical.Categories.2Functor.Base
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Slice.Base
open import Cubical.Categories.Constructions.Slice.Functor
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓC ℓC' ℓC'' ℓD ℓD' ℓD'' ℓE ℓE' : Level

open 2Category
open LaxFunctor
open PseudoFunctor
open GroupoidObjectsCategory
open isUnivalent

module _ {ℓC ℓC'} (C : Category ℓC ℓC') ℓD ℓD' where
  OpFibration : Type _
  OpFibration = PseudoFunctor (Cat→2Cat C) (CAT {ℓC = ℓD} {ℓC' = ℓD'})

  OpFibrationEq : Type _
  OpFibrationEq = PseudoFunctor (Cat→2CatEq C) (CAT {ℓC = ℓD} {ℓC' = ℓD'})

module _ {ℓC ℓC'} (C : Category ℓC ℓC') ℓD ℓD' where
  Fibration : Type _
  Fibration = OpFibration (C ^op) ℓD ℓD'

  FibrationEq : Type _
  FibrationEq = OpFibrationEq (C ^op) ℓD ℓD'

-- module _ {ℓC ℓC'} (C : Category ℓC ℓC') ℓD ℓD' where
--   module _ (F : Fibration C ℓD ℓD') {E : Category ℓE ℓE'} (G : Functor E C) where
--     private
--       module C = Category C
--       module E = Category E
--       module F = PseudoFunctor F
--       module G = Functor G
--       module CAT = 2Category (CAT {ℓC = ℓD} {ℓC' = ℓD'})

--     reindex : Fibration E ℓD ℓD'
--     reindex .lax .F₀ = λ z → F.F₀ (G.F-ob z)
--     reindex .lax .F₁ = λ z → F.F₁ (G.F-hom z)
--     reindex .lax .F₂ f≡g = F.F₂ (cong G.F-hom f≡g)
--     reindex .lax .F-id = seqTrans F.F-id (F.F₂ (sym G.F-id))
--     reindex .lax .F-seq f g =
--       seqTrans
--         (F.F-seq (G.F-hom f) (G.F-hom g))
--         (F.F₂ (sym $ G.F-seq g f))
--     reindex .lax .F-id₂ = F.F-id₂
--     reindex .lax .F-seqⱽ f≡g g≡h =
--       cong F.F₂ (C.isSetHom _ _ _ _)
--       ∙ F.F-seqⱽ (λ i → G.F-hom (f≡g i)) (λ i → G.F-hom (g≡h i))
--     reindex .lax .F-seqᴴ f≡f' g≡g' =
--       {!!}
--       ∙ cong₂ seqTrans (F.F-seqᴴ (cong G.F-hom f≡f') (cong G.F-hom g≡g')) refl
--       ∙ {!!}
--       ∙ {!!}
--     reindex .lax .F-unitality-l = {!!}
--     reindex .lax .F-unitality-r = {!!}
--     reindex .lax .F-associativity = {!!}
--     reindex .pseudo = {!!}



-- module _ {ℓC ℓC'}
--   (C : Category ℓC ℓC') (pb : Pullbacks C)
--   {{isUniv : isUnivalent C}}
--   where

--   private
--     module C = Category C
--   open BaseChange pb
--   open NatTrans

  -- CodomainFibration : Fibration C _ _
  -- CodomainFibration .lax .F₀ c .cat = SliceCat C c
  -- CodomainFibration .lax .F₀ c .groupoid-obs =
  --   isGroupoid-ob (preservesUnivalenceSlice C c)
  -- CodomainFibration .lax .F₁ f = f ＊
  -- CodomainFibration .lax .F₂ {f = f} {g = g} f≡g .N-ob (sliceob h) =
  -- -- subst (NatTrans _) (cong (_＊) f≡g) (idTrans _)
  --   slicehom
  --     (pullbackArrow g
  --       (pb (cospan _ _ _ f h) .Pullback.pbPr₁)
  --       (pb (cospan _ _ _ f h) .Pullback.pbPr₂)
  --       (cong₂ C._⋆_ refl (sym f≡g)
  --       ∙ pb _ .Pullback.pbCommutes))
  --     ((sym $ pullbackArrowPr₁ C (pb _) _ _
  --         (cong₂ C._⋆_ refl (sym f≡g) ∙ pb _ .Pullback.pbCommutes)))
  -- CodomainFibration .lax .F₂ {f = f} {g = g} f≡g .N-hom
  --   (slicehom s r) = {!!}
  -- CodomainFibration .lax .F-id = {!!}
  -- CodomainFibration .lax .F-seq = {!!}
  -- CodomainFibration .lax .F-id₂ = {!!}
  -- CodomainFibration .lax .F-seqⱽ = {!!}
  -- CodomainFibration .lax .F-seqᴴ = {!!}
  -- CodomainFibration .lax .F-unitality-l = {!!}
  -- CodomainFibration .lax .F-unitality-r = {!!}
  -- CodomainFibration .lax .F-associativity = {!!}
  -- CodomainFibration .pseudo = {!!}
