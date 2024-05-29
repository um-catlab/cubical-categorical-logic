{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Constructions.Reindex.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Limits.Terminal
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor
open UniversalElement
open UniversalElementᴰ
open CartesianOver

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

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where

  reindReflectsVerticalTerminal :
    ∀ c → VerticalTerminalAt Dᴰ (F ⟅ c ⟆)
    → VerticalTerminalAt (reindex Dᴰ F) c
  reindReflectsVerticalTerminal c 𝟙ᴰ .vertexᴰ = 𝟙ᴰ .vertexᴰ
  reindReflectsVerticalTerminal c 𝟙ᴰ .elementᴰ = 𝟙ᴰ .elementᴰ
  reindReflectsVerticalTerminal c 𝟙ᴰ .universalᴰ = 𝟙ᴰ .universalᴰ

  VerticalTerminalsReindex :
    VerticalTerminals Dᴰ
    → VerticalTerminals (reindex Dᴰ F)
  VerticalTerminalsReindex vta c =
    reindReflectsVerticalTerminal c (vta (F ⟅ c ⟆))

  module _ {termC : Terminal' C} where
    open Terminal'Notation termC
    LiftedTerminalReindex :
      VerticalTerminalAt Dᴰ (F ⟅ 𝟙 ⟆)
      → LiftedTerminal (reindex Dᴰ F) termC
    LiftedTerminalReindex 𝟙ᴰ =
      Vertical/𝟙→LiftedTerm _
        (reindReflectsVerticalTerminal (termC .vertex) 𝟙ᴰ)
