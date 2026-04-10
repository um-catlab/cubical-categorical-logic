{-# OPTIONS --lossy-unification #-}
-- Written by Claude
module Cubical.Categories.Double.Instances.Span.Associator where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback.Alt

open import Cubical.Categories.Double.Instances.Span.Base

module SpanAssociator {ℓC ℓC'}
  (C : Category ℓC ℓC')
  (pbs : Pullbacks C)
  where
  open SpanDefs C pbs
  private
    module C = Category C

  -- The four pullback modules for the associator
  module AssocPBs {x y z w : C.ob}
    (s : Span x y) (t : Span y z) (u : Span z w) where
    -- (s⋆t)⋆u: outer pullback
    module pb = PullbackNotation
      (pbs (pbπ₂ (pbs (s .snd .snd) (t .snd .fst)) C.⋆ t .snd .snd) (u .snd .fst))
    -- s⋆(t⋆u): outer pullback
    module pb' = PullbackNotation
      (pbs (s .snd .snd) (pbπ₁ (pbs (t .snd .snd) (u .snd .fst)) C.⋆ t .snd .fst))
    -- s⋆t: inner pullback
    module pb'' = PullbackNotation (pbs (s .snd .snd) (t .snd .fst))
    -- t⋆u: inner pullback
    module pb''' = PullbackNotation (pbs (t .snd .snd) (u .snd .fst))

  spanαᴴ : ∀ {x y z w}
    (s : Span x y) (t : Span y z) (u : Span z w) →
    SpanSquare (seqSpan (seqSpan s t) u) (seqSpan s (seqSpan t u)) C.id C.id
  spanαᴴ s t u =
    h ,
    C.⋆IdR _ ∙ sym (C.⋆Assoc _ _ _)
      ∙ C.⟨ sym pb'.pbβ₁ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _ ,
    C.⋆IdR _ ∙ C.⟨ sym pb'''.pbβ₂ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
      ∙ C.⟨ sym pb'.pbβ₂ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
    where
    open AssocPBs s t u
    g' = pb'''.pbIntro (pb.pbπ₁ C.⋆ pb''.pbπ₂) pb.pbπ₂
      (C.⋆Assoc _ _ _ ∙ pb.pbCommutes)
    abstract
      p : (pb.pbπ₁ C.⋆ pb''.pbπ₁) C.⋆ s .snd .snd ≡ g' C.⋆ pb'''.pbπ₁ C.⋆ t .snd .fst
      p = (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb''.pbCommutes ⟩
          ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ sym pb'''.pbβ₁ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _)
    h = pb'.pbIntro (pb.pbπ₁ C.⋆ pb''.pbπ₁) g' p

  spanαᴴ⁻ : ∀ {x y z w}
    (s : Span x y) (t : Span y z) (u : Span z w) →
    SpanSquare (seqSpan s (seqSpan t u)) (seqSpan (seqSpan s t) u) C.id C.id
  spanαᴴ⁻ s t u =
    h⁻ ,
    C.⋆IdR _ ∙ C.⟨ sym pb''.pbβ₁ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
      ∙ C.⟨ sym pb.pbβ₁ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _ ,
    C.⋆IdR _ ∙ sym (C.⋆Assoc _ _ _)
      ∙ C.⟨ sym pb.pbβ₂ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
    where
    open AssocPBs s t u
    abstract
      p : pb'.pbπ₁ C.⋆ s .snd .snd ≡ (pb'.pbπ₂ C.⋆ pb'''.pbπ₁) C.⋆ t .snd .fst
      p  = (pb'.pbCommutes ∙ sym (C.⋆Assoc _ _ _))

    f'⁻ = pb''.pbIntro pb'.pbπ₁ (pb'.pbπ₂ C.⋆ pb'''.pbπ₁) p

    abstract
      q : f'⁻ C.⋆ pb''.pbπ₂ C.⋆ t .snd .snd ≡ (pb'.pbπ₂ C.⋆ pb'''.pbπ₂) C.⋆ u .snd .fst
      q = (sym (C.⋆Assoc _ _ _) ∙ C.⟨ pb''.pbβ₂ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ pb'''.pbCommutes ⟩ ∙ sym (C.⋆Assoc _ _ _))

    h⁻ = pb.pbIntro f'⁻ (pb'.pbπ₂ C.⋆ pb'''.pbπ₂) q

  spanαᴴαᴴ⁻-apex : ∀ {x y z w}
    (s : Span x y) (t : Span y z) (u : Span z w) →
    spanαᴴ s t u .fst C.⋆ spanαᴴ⁻ s t u .fst ≡ C.id
  spanαᴴαᴴ⁻-apex s t u =
    pb.pbExtensionality
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb.pbβ₁ ⟩
        ∙ pb''.pbExtensionality
          (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb''.pbβ₁ ⟩ ∙ pb'.pbβ₁)
          (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb''.pbβ₂ ⟩
            ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ pb'.pbβ₂ ⟩⋆⟨ refl ⟩ ∙ pb'''.pbβ₁)
        ∙ sym (C.⋆IdL _))
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb.pbβ₂ ⟩
        ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ pb'.pbβ₂ ⟩⋆⟨ refl ⟩ ∙ pb'''.pbβ₂
        ∙ sym (C.⋆IdL _))
    where open AssocPBs s t u

  spanαᴴ⁻αᴴ-apex : ∀ {x y z w}
    (s : Span x y) (t : Span y z) (u : Span z w) →
    spanαᴴ⁻ s t u .fst C.⋆ spanαᴴ s t u .fst ≡ C.id
  spanαᴴ⁻αᴴ-apex s t u =
    pb'.pbExtensionality
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb'.pbβ₁ ⟩
        ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ pb.pbβ₁ ⟩⋆⟨ refl ⟩ ∙ pb''.pbβ₁
        ∙ sym (C.⋆IdL _))
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb'.pbβ₂ ⟩
        ∙ pb'''.pbExtensionality
          (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb'''.pbβ₁ ⟩
            ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ pb.pbβ₁ ⟩⋆⟨ refl ⟩ ∙ pb''.pbβ₂)
          (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb'''.pbβ₂ ⟩ ∙ pb.pbβ₂)
        ∙ sym (C.⋆IdL _))
    where open AssocPBs s t u

  spanαᴴ-nat-apex : ∀ {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄}
    {f₁ : Span x₁ x₂} {f₂ : Span x₂ x₃} {f₃ : Span x₃ x₄}
    {g₁ : Span y₁ y₂} {g₂ : Span y₂ y₃} {g₃ : Span y₃ y₄}
    {v₁ : C [ x₁ , y₁ ]} {v₂ : C [ x₂ , y₂ ]}
    {v₃ : C [ x₃ , y₃ ]} {v₄ : C [ x₄ , y₄ ]}
    (α₁ : SpanSquare f₁ g₁ v₁ v₂) (α₂ : SpanSquare f₂ g₂ v₂ v₃)
    (α₃ : SpanSquare f₃ g₃ v₃ v₄) →
    seqᴴSq (seqᴴSq α₁ α₂) α₃ .fst C.⋆ spanαᴴ g₁ g₂ g₃ .fst
      ≡ spanαᴴ f₁ f₂ f₃ .fst C.⋆ seqᴴSq α₁ (seqᴴSq α₂ α₃) .fst
  spanαᴴ-nat-apex {f₁ = f₁} {f₂} {f₃} {g₁} {g₂} {g₃} α₁ α₂ α₃ =
    G.pb'.pbExtensionality π₁-eq (G.pb'''.pbExtensionality π₂₁-eq π₂₂-eq)
    where
    module F = AssocPBs f₁ f₂ f₃
    module G = AssocPBs g₁ g₂ g₃
    -- π₁: both sides → F.pb.pbπ₁ ⋆ (F.pb''.pbπ₁ ⋆ α₁ .fst)
    π₁-eq =
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb'.pbβ₁ ⟩
        ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ G.pb.pbβ₁ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb''.pbβ₁ ⟩)
      ∙ sym
        (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb'.pbβ₁ ⟩
        ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ F.pb'.pbβ₁ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _)
    -- π₂∘π₁: both sides → F.pb.pbπ₁ ⋆ (F.pb''.pbπ₂ ⋆ α₂ .fst)
    π₂₁-eq =
      (C.⟨ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb'.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb'''.pbβ₁ ⟩
        ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ G.pb.pbβ₁ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb''.pbβ₂ ⟩)
      ∙ sym
        (C.⟨ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb'.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb'''.pbβ₁ ⟩ ⟩
        ∙ C.⟨ refl ⟩⋆⟨ sym (C.⋆Assoc _ _ _) ⟩
        ∙ sym (C.⋆Assoc _ _ _)
        ∙ C.⟨ sym (C.⋆Assoc _ _ _) ∙ C.⟨ F.pb'.pbβ₂ ⟩⋆⟨ refl ⟩
            ∙ F.pb'''.pbβ₁ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _)
    -- π₂∘π₂: both sides → F.pb.pbπ₂ ⋆ α₃ .fst
    π₂₂-eq =
      (C.⟨ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb'.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb'''.pbβ₂ ⟩
        ∙ G.pb.pbβ₂)
      ∙ sym
        (C.⟨ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb'.pbβ₂ ⟩ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _
        ∙ C.⟨ refl ⟩⋆⟨ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ G.pb'''.pbβ₂ ⟩ ⟩
        ∙ C.⟨ refl ⟩⋆⟨ sym (C.⋆Assoc _ _ _) ⟩
        ∙ sym (C.⋆Assoc _ _ _)
        ∙ C.⟨ sym (C.⋆Assoc _ _ _) ∙ C.⟨ F.pb'.pbβ₂ ⟩⋆⟨ refl ⟩
            ∙ F.pb'''.pbβ₂ ⟩⋆⟨ refl ⟩)
