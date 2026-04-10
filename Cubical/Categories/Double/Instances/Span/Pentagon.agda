{-# OPTIONS --lossy-unification #-}
-- Written by Claude
module Cubical.Categories.Double.Instances.Span.Pentagon where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback.Alt

open import Cubical.Categories.Double.Instances.Span.Base
open import Cubical.Categories.Double.Instances.Span.Associator

module SpanPentagon {ℓC ℓC'}
  (C : Category ℓC ℓC')
  (pbs : Pullbacks C)
  where
  open SpanDefs C pbs
  open SpanAssociator C pbs
  private
    module C = Category C

  spanPentagon-apex : ∀ {v w x y z}
    (f : Span v w) (g : Span w x) (h : Span x y) (k : Span y z) →
    spanαᴴ (seqSpan f g) h k .fst C.⋆ spanαᴴ f g (seqSpan h k) .fst
      ≡ seqᴴSq (spanαᴴ f g h) (idⱽSq {s = k}) .fst
        C.⋆ (spanαᴴ f (seqSpan g h) k .fst
        C.⋆ seqᴴSq (idⱽSq {s = f}) (spanαᴴ g h k) .fst)
  spanPentagon-apex f g h k =
    A2.pb'.pbExtensionality π₁-eq
      (A2.pb'''.pbExtensionality π₂₁-eq
        (A1.pb'''.pbExtensionality π₂₂₁-eq π₂₂₂-eq))
    where
    module A1 = AssocPBs (seqSpan f g) h k
    module A2 = AssocPBs f g (seqSpan h k)
    module A3 = AssocPBs f g h
    module A4 = AssocPBs f (seqSpan g h) k
    module A5 = AssocPBs g h k

    π₁-eq =
      -- LHS → A1.pb.π₁ ⋆ (A1.pb''.π₁ ⋆ A2.pb''.π₁)
      (C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ A2.pb'.pbβ₁ ⟩
      ∙ sym (C.⋆Assoc _ _ _)
      ∙ C.⟨ A1.pb'.pbβ₁ ⟩⋆⟨ refl ⟩
      ∙ C.⋆Assoc _ _ _)
      ∙ sym
      -- RHS → A1.pb.π₁ ⋆ (A1.pb''.π₁ ⋆ A2.pb''.π₁)
      (C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⟨ refl ⟩⋆⟨ A2.pb'.pbβ₁ ⟩ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⟨ refl ⟩⋆⟨ C.⋆IdR _ ⟩ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ A4.pb'.pbβ₁ ⟩
      ∙ sym (C.⋆Assoc _ _ _)
      ∙ C.⟨ A4.pb.pbβ₁ ⟩⋆⟨ refl ⟩
      ∙ C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ A3.pb'.pbβ₁ ⟩)

    π₂₁-eq =
      -- LHS → A1.pb.π₁ ⋆ (A1.pb''.π₁ ⋆ A2.pb''.π₂)
      (C.⟨ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ A2.pb'.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
      ∙ C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ A2.pb'''.pbβ₁ ⟩
      ∙ sym (C.⋆Assoc _ _ _)
      ∙ C.⟨ A1.pb'.pbβ₁ ⟩⋆⟨ refl ⟩
      ∙ C.⋆Assoc _ _ _)
      ∙ sym
      -- RHS → A1.pb.π₁ ⋆ (A1.pb''.π₁ ⋆ A2.pb''.π₂)
      (C.⟨ C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
          ∙ C.⟨ refl ⟩⋆⟨ C.⟨ refl ⟩⋆⟨ A2.pb'.pbβ₂ ⟩ ⟩
          ∙ C.⟨ refl ⟩⋆⟨ sym (C.⋆Assoc _ _ _) ⟩
          ∙ C.⟨ refl ⟩⋆⟨ C.⟨ A4.pb'.pbβ₂ ⟩⋆⟨ refl ⟩ ⟩
        ⟩⋆⟨ refl ⟩
      ∙ C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⟨ refl ⟩⋆⟨ A2.pb'''.pbβ₁ ⟩ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ sym (C.⋆Assoc _ _ _) ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⟨ A4.pb'''.pbβ₁ ⟩⋆⟨ refl ⟩ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
      ∙ sym (C.⋆Assoc _ _ _)
      ∙ C.⟨ A4.pb.pbβ₁ ⟩⋆⟨ refl ⟩
      ∙ C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ sym (C.⋆Assoc _ _ _) ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⟨ A3.pb'.pbβ₂ ⟩⋆⟨ refl ⟩ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ A3.pb'''.pbβ₁ ⟩)

    π₂₂₁-eq =
      -- LHS chain → A1.pb.π₁ ⋆ A1.pb''.π₂
      (C.⟨ C.⟨ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ A2.pb'.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ A2.pb'''.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
      ∙ C.⟨ A1.pb'.pbβ₂ ⟩⋆⟨ refl ⟩
      ∙ A1.pb'''.pbβ₁)
      ∙ sym
      -- RHS chain → A1.pb.π₁ ⋆ A1.pb''.π₂
      (C.⟨ C.⟨ C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
          ∙ C.⟨ refl ⟩⋆⟨ C.⟨ refl ⟩⋆⟨ A2.pb'.pbβ₂ ⟩ ⟩
          ∙ C.⟨ refl ⟩⋆⟨ sym (C.⋆Assoc _ _ _) ⟩
          ∙ C.⟨ refl ⟩⋆⟨ C.⟨ A4.pb'.pbβ₂ ⟩⋆⟨ refl ⟩ ⟩
        ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
        ∙ C.⟨ refl ⟩⋆⟨ C.⟨ refl ⟩⋆⟨ A2.pb'''.pbβ₂ ⟩ ⟩
      ⟩⋆⟨ refl ⟩
      ∙ C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⟨ refl ⟩⋆⟨ A1.pb'''.pbβ₁ ⟩ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ sym (C.⋆Assoc _ _ _) ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⟨ A4.pb'''.pbβ₁ ⟩⋆⟨ refl ⟩ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
      ∙ sym (C.⋆Assoc _ _ _)
      ∙ C.⟨ A4.pb.pbβ₁ ⟩⋆⟨ refl ⟩
      ∙ C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ sym (C.⋆Assoc _ _ _) ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⟨ A3.pb'.pbβ₂ ⟩⋆⟨ refl ⟩ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ A3.pb'''.pbβ₂ ⟩)

    π₂₂₂-eq =
      (C.⟨ C.⟨ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ A2.pb'.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ A2.pb'''.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
      ∙ C.⟨ A1.pb'.pbβ₂ ⟩⋆⟨ refl ⟩
      ∙ A1.pb'''.pbβ₂)
      ∙ sym
      (C.⟨ C.⟨ C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
          ∙ C.⟨ refl ⟩⋆⟨ C.⟨ refl ⟩⋆⟨ A2.pb'.pbβ₂ ⟩ ⟩
          ∙ C.⟨ refl ⟩⋆⟨ sym (C.⋆Assoc _ _ _) ⟩
          ∙ C.⟨ refl ⟩⋆⟨ C.⟨ A4.pb'.pbβ₂ ⟩⋆⟨ refl ⟩ ⟩
        ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
        ∙ C.⟨ refl ⟩⋆⟨ C.⟨ refl ⟩⋆⟨ A2.pb'''.pbβ₂ ⟩ ⟩
      ⟩⋆⟨ refl ⟩
      ∙ C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ C.⟨ refl ⟩⋆⟨ A1.pb'''.pbβ₂ ⟩ ⟩
      ∙ C.⟨ refl ⟩⋆⟨ A4.pb'''.pbβ₂ ⟩
      ∙ A4.pb.pbβ₂ ∙ C.⋆IdR _)
