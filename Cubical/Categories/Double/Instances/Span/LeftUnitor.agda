{-# OPTIONS --lossy-unification #-}
-- Written by Claude
module Cubical.Categories.Double.Instances.Span.LeftUnitor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback.Alt

open import Cubical.Categories.Double.Instances.Span.Base

module SpanLeftUnitor {ℓC ℓC'}
  (C : Category ℓC ℓC')
  (pbs : Pullbacks C)
  where
  open SpanDefs C pbs
  private
    module C = Category C

  spanλᴴ : ∀ {x y} (s : Span x y) →
    SpanSquare (seqSpan idSpan s) s C.id C.id
  spanλᴴ {x = x} (xy , f , g) =
    pb.pbπ₂ ,
    C.⋆IdR _ ∙ pb.pbCommutes ,
    C.⋆IdR _
    where module pb = PullbackNotation (pbs (C.id {x = x}) f)

  spanλᴴ⁻ : ∀ {x y} (s : Span x y) →
    SpanSquare s (seqSpan idSpan s) C.id C.id
  spanλᴴ⁻ {x = x} (xy , f , g) =
    pb.pbIntro f C.id (C.⋆IdR _ ∙ sym (C.⋆IdL _)) ,
    C.⟨ sym pb.pbβ₁ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _ ,
    C.⋆IdR _ ∙ sym (C.⋆IdL _) ∙ C.⟨ sym pb.pbβ₂ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
    where
    module pb = PullbackNotation (pbs (C.id {x = x}) f)

  spanλᴴλᴴ⁻-apex : ∀ {x y} (s : Span x y) →
    spanλᴴ s .fst C.⋆ spanλᴴ⁻ s .fst ≡ C.id
  spanλᴴλᴴ⁻-apex {x = x} (xy , f , g) =
    pb.pbExtensionality
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb.pbβ₁ ⟩
        ∙ sym pb.pbCommutes ∙ C.⋆IdR _ ∙ sym (C.⋆IdL _))
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb.pbβ₂ ⟩ ∙ C.⋆IdR _ ∙ sym (C.⋆IdL _))
    where
    module pb = PullbackNotation (pbs (C.id {x = x}) f)

  spanλᴴ⁻λᴴ-apex : ∀ {x y} (s : Span x y) →
    spanλᴴ⁻ s .fst C.⋆ spanλᴴ s .fst ≡ C.id
  spanλᴴ⁻λᴴ-apex {x = x} (xy , f , g) = pb.pbβ₂
    where module pb = PullbackNotation (pbs (C.id {x = x}) f)
