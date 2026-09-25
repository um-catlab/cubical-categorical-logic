open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Enriched.Enrichment.Base renaming (Enrichment to VE)

-- Enrichment of functors, following "Univalent Enriched Categories and the Enriched Rezk Completion" (v.d. Weide 2026)
module Cubical.Categories.Enriched.Enrichment.Functor.Base
  {ℓV ℓV' ℓC ℓC' ℓD ℓD' : Level}
  (V : MonoidalCategory ℓV ℓV')
  (C : Category ℓC ℓC')
  (D : Category ℓD ℓD')
  (ℰC : VE C V)
  (ℰD : VE D V)
  (F : Functor C D)
  where

open import Cubical.Foundations.Isomorphism

open Functor F

record Enrichment : Type (ℓ-max (ℓ-max ℓV ℓV') (ℓ-max ℓC ℓC')) where
   private
     module C = Category C
     module D = Category D
     module V = MonoidalCategory V
     module ℰD = VE ℰD
     module ℰC = VE ℰC
     open VE ℰC renaming (VE[_,_] to ℰC[_,_])
     open VE ℰD renaming (VE[_,_] to ℰD[_,_])

   field
      F[_,_] : ∀ x y → V.Hom[ ℰC[ x , y ] , ℰD[ F-ob x , F-ob y ] ]
      F-id : {X : C.ob} → (ℰC.id {X} V.⋆  F[ X , X ]) ≡ ℰD.id {F-ob X}
      F-seq : {X Y Z : C.ob} →
        (F[ X , Y ] V.⊗ₕ F[ Y , Z ]) V.⋆ ℰD.seq (F-ob X) (F-ob Y) (F-ob Z)
        ≡
        ℰC.seq X Y Z V.⋆ F[ X , Z ]
      agree : ∀ {x y} → ∀ (f : C.Hom[ x , y ]) →
        ℰD.⌜ F-hom f ⌝ ≡ ℰC.⌜ f ⌝ V.⋆ F[ x , y ]
