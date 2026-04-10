{-# OPTIONS --lossy-unification #-}
-- Double category of spans for a category with pullbacks
module Cubical.Categories.Double.Instances.Span where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback.Alt

open import Cubical.Categories.Displayed.Base

open import Cubical.Categories.Double.Base

-- For performance reasons, these needed to be all in separate files
open import Cubical.Categories.Double.Instances.Span.Base
open import Cubical.Categories.Double.Instances.Span.LeftUnitor
open import Cubical.Categories.Double.Instances.Span.RightUnitor
open import Cubical.Categories.Double.Instances.Span.Associator
open import Cubical.Categories.Double.Instances.Span.Pentagon
open import Cubical.Categories.Double.Instances.Span.Triangle
open import Cubical.Categories.Double.Instances.Span.Interchange

open DoubleCategory
open Categoryᴰ

module _ {ℓC ℓC'}
  (C : Category ℓC ℓC')
  (pbs : Pullbacks C)
  where
  private
    module C = Category C

  open SpanDefs C pbs
  open SpanLeftUnitor C pbs
  open SpanRightUnitor C pbs
  open SpanAssociator C pbs
  open SpanTriangle C pbs
  open SpanPentagon C pbs
  open SpanInterchange C pbs
  open PullbackNotation

  SPAN : DoubleCategory _ _ _ _
  SPAN .ob = C.ob
  SPAN .Homⱽ[_,_] = C.Hom[_,_]
  SPAN .idⱽ = C.id
  SPAN ._⋆ⱽ_ = C._⋆_
  SPAN .⋆ⱽIdL = C.⋆IdL
  SPAN .⋆ⱽIdR = C.⋆IdR
  SPAN .⋆ⱽAssoc = C.⋆Assoc
  SPAN .Homᴴ[_,_] = Span
  SPAN .idᴴ = idSpan
  SPAN ._⋆ᴴ_ = seqSpan
  SPAN .Sq = SpanSquare
  SPAN .isSetSq = isSetΣ C.isSetHom
    (λ _ → isSet× (isProp→isSet $ C.isSetHom _ _) (isProp→isSet $ C.isSetHom _ _))
  SPAN .DoubleCategory.idⱽSq = SpanDefs.idⱽSq C pbs
  SPAN .idᴴSq {v = v} = v , (C.⋆IdL _ ∙ sym (C.⋆IdR _)) , (C.⋆IdL _ ∙ sym (C.⋆IdR _))
  SPAN ._⋆ⱽSq_ = seqⱽSq
  SPAN .⋆ⱽIdLSq _ = makeSpanSquarePathP (C.⋆IdL _)
  SPAN .⋆ⱽIdRSq _ = makeSpanSquarePathP (C.⋆IdR _)
  SPAN .⋆ⱽAssocSq _ _ _ = makeSpanSquarePathP (C.⋆Assoc _ _ _)
  SPAN ._⋆ᴴSq_ = seqᴴSq
  -- Left unitor
  SPAN .λᴴ = spanλᴴ
  SPAN .λᴴ⁻ = spanλᴴ⁻
  SPAN .λᴴλᴴ⁻ s = makeSpanSquarePathP (spanλᴴλᴴ⁻-apex s)
  SPAN .λᴴ⁻λᴴ s = makeSpanSquarePathP (spanλᴴ⁻λᴴ-apex s)
  SPAN .λᴴ-nat {f = xyf} {g = zwg} {v = v} {u = u} sq =
    makeSpanSquarePathP $
      C.⟨ pbg.pbIntro≡ (sym (pbg.pbβ₁
        {e = C.⋆IdR _ ∙ (C.⟨ (sym $ C.⋆IdR _) ∙ pbf.pbCommutes ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _)
          ∙ C.⟨ refl ⟩⋆⟨ sq .snd .fst ⟩ ∙ sym (C.⋆Assoc _ _ _)}))
        (sym pbg.pbβ₂) ⟩⋆⟨ refl ⟩ ∙ pbg.pbβ₂
    where
    module pbf = PullbackNotation (pbs (C.id {x = _}) (xyf .snd .fst))
    module pbg = PullbackNotation (pbs (C.id {x = _}) (zwg .snd .fst))
  -- Right unitor
  SPAN .ρᴴ = spanρᴴ
  SPAN .ρᴴ⁻ = spanρᴴ⁻
  SPAN .ρᴴρᴴ⁻ s = makeSpanSquarePathP (spanρᴴρᴴ⁻-apex s)
  SPAN .ρᴴ⁻ρᴴ s = makeSpanSquarePathP (spanρᴴ⁻ρᴴ-apex s)
  SPAN .ρᴴ-nat {f = xyf} {g = zwg} sq =
    makeSpanSquarePathP pbg.pbβ₁
    where
    module pbg = PullbackNotation (pbs (zwg .snd .snd) (C.id {x = _}))
  -- Associator
  SPAN .αᴴ = spanαᴴ
  SPAN .αᴴ⁻ = spanαᴴ⁻
  SPAN .αᴴαᴴ⁻ s t u = makeSpanSquarePathP (spanαᴴαᴴ⁻-apex s t u)
  SPAN .αᴴ⁻αᴴ s t u = makeSpanSquarePathP (spanαᴴ⁻αᴴ-apex s t u)
  SPAN .αᴴ-nat α₁ α₂ α₃ = makeSpanSquarePathP (spanαᴴ-nat-apex α₁ α₂ α₃)
  -- Coherence
  SPAN .pentagon f g h k = makeSpanSquarePathP (spanPentagon-apex f g h k)
  SPAN .triangle f g = makeSpanSquarePathP (spanTriangle-apex f g)
  SPAN .interchange ul ur dl dr = makeSpanSquarePathP (spanInterchange-apex ul ur dl dr)
