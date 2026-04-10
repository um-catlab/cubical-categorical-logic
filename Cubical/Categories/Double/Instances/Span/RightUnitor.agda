{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Double.Instances.Span.RightUnitor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback.Alt

open import Cubical.Categories.Double.Instances.Span.Base

module SpanRightUnitor {ℓC ℓC'}
  (C : Category ℓC ℓC')
  (pbs : Pullbacks C)
  where
  open SpanDefs C pbs
  private
    module C = Category C

  spanρᴴ : ∀ {x y} (s : Span x y) →
    SpanSquare (seqSpan s idSpan) s C.id C.id
  spanρᴴ (xy , f , g) =
    pb.pbπ₁ , C.⋆IdR _ , C.⋆IdR _ ∙ sym pb.pbCommutes
    where module pb = PullbackNotation (pbs g C.id)

  spanρᴴ⁻ : ∀ {x y} (s : Span x y) →
    SpanSquare s (seqSpan s idSpan) C.id C.id
  spanρᴴ⁻ (xy , f , g) =
    pb.pbIntro C.id g (C.⋆IdL _ ∙ sym (C.⋆IdR _)) ,
    C.⋆IdR _ ∙ sym (C.⋆IdL _) ∙ C.⟨ sym pb.pbβ₁ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _ ,
    C.⟨ sym pb.pbβ₂ ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
    where module pb = PullbackNotation (pbs g C.id)

  spanρᴴρᴴ⁻-apex : ∀ {x y} (s : Span x y) →
    spanρᴴ s .fst C.⋆ spanρᴴ⁻ s .fst ≡ C.id
  spanρᴴρᴴ⁻-apex (xy , f , g) =
    pb.pbExtensionality
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb.pbβ₁ ⟩ ∙ C.⋆IdR _ ∙ sym (C.⋆IdL _))
      (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb.pbβ₂ ⟩
        ∙ pb.pbCommutes ∙ C.⋆IdR _ ∙ sym (C.⋆IdL _))
    where module pb = PullbackNotation (pbs g C.id)

  spanρᴴ⁻ρᴴ-apex : ∀ {x y} (s : Span x y) →
    spanρᴴ⁻ s .fst C.⋆ spanρᴴ s .fst ≡ C.id
  spanρᴴ⁻ρᴴ-apex (xy , f , g) = pb.pbβ₁
    where module pb = PullbackNotation (pbs g C.id)
