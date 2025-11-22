module Cubical.Categories.Enriched.Functors.Base where

open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Functor
open EnrichedCategory
open Functor

module _ {ℓV ℓV'  : Level} (V : MonoidalCategory ℓV ℓV') where
  private 
    module V = MonoidalCategory V

  record EnrichedFunctor
    {ℓE ℓD : Level}
    (E : EnrichedCategory V ℓE)
    (D : EnrichedCategory V ℓD) :
      Type (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') (ℓ-suc ℓE)) (ℓ-suc ℓD)) where
    private module E = EnrichedCategory E
    private module D = EnrichedCategory D
    field
      F₀ : E.ob → D.ob
      F₁ : {X Y : E.ob} → V.Hom[ E.Hom[ X , Y ] , D.Hom[ F₀ X , F₀ Y ] ]
      Fid : {X : E.ob} → (E.id {X} V.⋆  F₁ {X} {X}) ≡ D.id {F₀ X}
      Fseq : {X Y Z : E.ob} →
        (F₁ {X} {Y} V.⊗ₕ F₁ {Y} {Z}) V.⋆ D.seq (F₀ X) (F₀ Y) (F₀ Z)
        ≡
        E.seq X Y Z V.⋆ F₁ {X} {Z}


  open EnrichedFunctor

  eseq : {ℓC ℓD ℓE : Level}→ 
    {C : EnrichedCategory V ℓC} →
    {D : EnrichedCategory V ℓD} →
    {E : EnrichedCategory V ℓE} → 
    EnrichedFunctor C D → EnrichedFunctor D E → EnrichedFunctor C E
  eseq  F G .F₀ c = F₀ G (F₀ F c)
  eseq  F G .F₁ = F₁ F V.⋆ F₁ G
  eseq  {C} F G .Fid =
    (sym (V.⋆Assoc _ _ _) ∙ cong (λ h → h V.⋆ F₁ G) (F .Fid) ) ∙ G .Fid
  eseq  {C} F G .Fseq =
    ((((cong₂ V._⋆_ (V.─⊗─ .F-seq _ _) refl ∙ V.⋆Assoc _ _ _ )
    ∙ cong (λ h → (F₁ F V.⊗ₕ F₁ F) V.⋆ h ) (G .Fseq))
    ∙ sym (V.⋆Assoc _ _ _))
    ∙ cong (λ h → h V.⋆ F₁ G) (F .Fseq))
    ∙ V.⋆Assoc _ _ _