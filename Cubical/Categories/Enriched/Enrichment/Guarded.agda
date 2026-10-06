module Cubical.Categories.Enriched.Enrichment.Guarded where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.NaturalTransformation.Base
open import Cubical.Categories.Monoidal.Guarded
open import Cubical.Categories.Enriched.Enrichment.Base

private
  variable
    ℓV ℓV' ℓC ℓC' : Level

module EnrichedLöb {V : MonoidalCategory ℓV ℓV'} (G : GuardedModel V)
  {C : Category ℓC ℓC'} (ℰ : Enrichment C V) where
  private
    module V = MonoidalCategory V
    module C = Category C
    module ℰ = Enrichment ℰ
    open GuardedModel G

  module _ {X Y : C.ob} (φ : V.Hom[ ▷F ℰ.VE[ X , Y ] , ℰ.VE[ X , Y ] ]) where
    löb : C [ X , Y ]
    löb = ℰ.⌞ fix φ ⌟

    löb-fix : ℰ.⌜ löb ⌝ ≡ (ℰ.⌜ löb ⌝ V.⋆ next⟦ ℰ.VE[ X , Y ] ⟧) V.⋆ φ
    löb-fix =
      ℰ.⇄-agree← (fix φ)
      ∙ fix-fix φ
      ∙ cong (λ u → (u V.⋆ next⟦ ℰ.VE[ X , Y ] ⟧) V.⋆ φ) (sym (ℰ.⇄-agree← (fix φ)))

    löb-uniq : (h : C [ X , Y ])
      → ℰ.⌜ h ⌝ ≡ (ℰ.⌜ h ⌝ V.⋆ next⟦ ℰ.VE[ X , Y ] ⟧) V.⋆ φ
      → h ≡ löb
    löb-uniq h p = sym (ℰ.⇄-agree→ h) ∙ cong ℰ.⌞_⌟ (fix-uniq φ ℰ.⌜ h ⌝ p)
