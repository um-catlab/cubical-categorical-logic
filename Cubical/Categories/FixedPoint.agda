-- Categorical abstraction of a fixed-point
--
-- This is a diagrammatic concept, a fixed point is equivalent to a
-- functor out of the initial category with a fixed point:
--
-- 1 -[ fix f ]-> x -[ f ]-> x
--          =
-- 1 ------[ fix f ]-------> x
module Cubical.Categories.FixedPoint where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open Category
open Functor

module _ {ℓ ℓ'} (C : Category ℓ ℓ') (𝟙 : C .ob) where
  private
    module C = Category C
  fixed-point : {x : C .ob} → C [ x , x ] → Type _
  fixed-point {x} f = Σ[ fix⟨f⟩ ∈ C [ 𝟙 , x ] ] (fix⟨f⟩ C.⋆ f) ≡ fix⟨f⟩

  -- TODO: A fixed-point is a diagram so it is preserved by all
  -- functors

module _ {ℓ ℓ'} (C : Category ℓ ℓ') (x : C .ob) where
  id-fixed-point : fixed-point C x (C .id {x})
  id-fixed-point = (id C) , (⋆IdL C (id C))

module _ {ℓC ℓC' ℓD ℓD'}
  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {𝟙 x : C .ob} {f : C [ x , x ]}
  (F : Functor C D)
  where
  private
    module C = Category C
  F-hom-fixed-point :
    fixed-point C 𝟙 f
    → fixed-point D (F ⟅ 𝟙 ⟆) (F ⟪ f ⟫)
  F-hom-fixed-point fix⟨f⟩ .fst = F .Functor.F-hom (fix⟨f⟩ .fst)
  F-hom-fixed-point fix⟨f⟩ .snd = sym (F .F-seq _ _)
    ∙ cong (F .F-hom) (fix⟨f⟩ .snd)
