{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Double.Instances.Span.Triangle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback.Alt

open import Cubical.Categories.Double.Instances.Span.Base
open import Cubical.Categories.Double.Instances.Span.LeftUnitor
open import Cubical.Categories.Double.Instances.Span.RightUnitor
open import Cubical.Categories.Double.Instances.Span.Associator

module SpanTriangle {ℓC ℓC'}
  (C : Category ℓC ℓC')
  (pbs : Pullbacks C)
  where
  open SpanDefs C pbs
  open SpanLeftUnitor C pbs
  open SpanRightUnitor C pbs
  open SpanAssociator C pbs
  private
    module C = Category C

  spanTriangle-apex : ∀ {x y z}
    (f : Span x y) (g : Span y z) →
    spanαᴴ f idSpan g .fst C.⋆ seqᴴSq (idⱽSq {s = f}) (spanλᴴ g) .fst
      ≡ seqᴴSq (spanρᴴ f) (idⱽSq {s = g}) .fst
  spanTriangle-apex f g =
    pb_fg.pbExtensionality
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb_fg.pbβ₁ ⟩
        ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ pb'.pbβ₁ ⟩⋆⟨ refl ⟩
        ∙ C.⋆IdR _
        ∙ sym pb_fg.pbβ₁)
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb_fg.pbβ₂ ⟩
        ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ pb'.pbβ₂ ⟩⋆⟨ refl ⟩
        ∙ pb'''.pbβ₂
        ∙ sym (C.⋆IdR _) ∙ sym pb_fg.pbβ₂)
    where
    open AssocPBs f idSpan g
    module pb_fg = PullbackNotation (pbs (f .snd .snd) (g .snd .fst))
