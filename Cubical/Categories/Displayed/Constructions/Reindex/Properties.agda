{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Constructions.Reindex.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Fibration.Base

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor

{- -}
module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D
    F*Dᴰ = reindex Dᴰ F
    module R = HomᴰReasoning Dᴰ
    module F*Dᴰ = Categoryᴰ F*Dᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  module _
    {c : C .ob}{c' : C .ob}
    {dᴰ' : Dᴰ.ob[ F ⟅ c' ⟆ ]}{f : C [ c , c' ]}
    where
    open CartesianOver
    reflectsCartesianOvers
      : CartesianOver Dᴰ dᴰ' (F ⟪ f ⟫)
      → CartesianOver F*Dᴰ dᴰ' f
    reflectsCartesianOvers f-lift .f*cᴰ' = f-lift .f*cᴰ'
    reflectsCartesianOvers f-lift .π = f-lift .π
    reflectsCartesianOvers f-lift .isCartesian {c''} dᴰ'' g gfᴰ = uniqueExists
      (⟨gfᴰ⟩' .fst .fst)
      ⟨gfᴰ⟩'-commutes
      (λ _ → F*Dᴰ.isSetHomᴰ _ _)
      ⟨gfᴰ⟩'-uniq
      where
        gfᴰ' : Dᴰ.Hom[ _ ][ dᴰ'' , dᴰ' ]
        gfᴰ' = R.reind (F .F-seq g f) gfᴰ

        ⟨gfᴰ⟩' = f-lift .isCartesian dᴰ'' (F ⟪ g ⟫) gfᴰ'

        ⟨gfᴰ⟩'-commutes : ⟨gfᴰ⟩' .fst .fst F*Dᴰ.⋆ᴰ f-lift .π ≡ gfᴰ
        ⟨gfᴰ⟩'-commutes = R.≡[]-rectify (R.≡[]∙ _ _ (R.≡[]∙ _ _
          (R.reind-filler-sym (F .F-seq g f) _)
          (⟨gfᴰ⟩' .fst .snd))
          (symP (R.reind-filler (F .F-seq g f) gfᴰ)))

        ⟨gfᴰ⟩'-uniq
          : (gᴰ : F*Dᴰ.Hom[ g ][ dᴰ'' , f-lift .f*cᴰ' ])
          → (gᴰ F*Dᴰ.⋆ᴰ f-lift .π) ≡ gfᴰ
          → ⟨gfᴰ⟩' .fst .fst ≡ gᴰ
        ⟨gfᴰ⟩'-uniq gᴰ gᴰ-commutes = cong fst (⟨gfᴰ⟩' .snd (gᴰ ,
          (R.≡[]-rectify (R.≡[]∙ _ _ (R.≡[]∙ _ _
            (R.reind-filler (sym (F .F-seq _ _)) _)
            gᴰ-commutes)
            (R.reind-filler (F .F-seq g f) gfᴰ)))))
