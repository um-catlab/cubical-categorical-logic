{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Double.Instances.Span.Interchange where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback.Alt

open import Cubical.Categories.Double.Instances.Span.Base

module SpanInterchange {ℓC ℓC'}
  (C : Category ℓC ℓC')
  (pbs : Pullbacks C)
  where
  open SpanDefs C pbs
  private
    module C = Category C

  spanInterchange-apex : ∀ {u1 u2 u3 m1 m2 m3 d1 d2 d3}
    {↑f : Span u1 u2} {↑f' : Span u2 u3}
    {↓f : Span d1 d2} {↓f' : Span d2 d3}
    {←f : C [ u1 , m1 ]} {←f' : C [ m1 , d1 ]}
    {→f : C [ u3 , m3 ]} {→f' : C [ m3 , d3 ]}
    {←g : Span m1 m2} {↑g : C [ u2 , m2 ]}
    {→g : Span m2 m3} {↓g : C [ m2 , d2 ]}
    (ul : SpanSquare ↑f ←g ←f ↑g) (ur : SpanSquare ↑f' →g ↑g →f)
    (dl : SpanSquare ←g ↓f ←f' ↓g) (dr : SpanSquare →g ↓f' ↓g →f') →
    seqᴴSq (seqⱽSq ul dl) (seqⱽSq ur dr) .fst
      ≡ seqⱽSq (seqᴴSq ul ur) (seqᴴSq dl dr) .fst
  spanInterchange-apex {↑f = ↑f} {↑f' = ↑f'} {↓f = ↓f} {↓f' = ↓f'}
      {←g = ←g} {→g = →g} ul ur dl dr =
    pb↓.pbIntro≡
      (sym (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb↓.pbβ₁ ⟩
        ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ pbm.pbβ₁ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _))
      (sym (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pb↓.pbβ₂ ⟩
        ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ pbm.pbβ₂ ⟩⋆⟨ refl ⟩
        ∙ C.⋆Assoc _ _ _))
    where
    module pb↓ = PullbackNotation (pbs (↓f .snd .snd) (↓f' .snd .fst))
    module pbm = PullbackNotation (pbs (←g .snd .snd) (→g .snd .fst))
