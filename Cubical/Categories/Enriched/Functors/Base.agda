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
      F-ob : E.ob → D.ob
      F-hom : {X Y : E.ob} → V.Hom[ E.Hom[ X , Y ] , D.Hom[ F-ob X , F-ob Y ] ]
      F-id : {X : E.ob} → (E.id {X} V.⋆  F-hom {X} {X}) ≡ D.id {F-ob X}
      F-seq : {X Y Z : E.ob} →
        (F-hom {X} {Y} V.⊗ₕ F-hom {Y} {Z}) V.⋆ D.seq (F-ob X) (F-ob Y) (F-ob Z)
        ≡
        E.seq X Y Z V.⋆ F-hom {X} {Z}

  open EnrichedFunctor

  eseq : {ℓC ℓD ℓE : Level}→
    {C : EnrichedCategory V ℓC} →
    {D : EnrichedCategory V ℓD} →
    {E : EnrichedCategory V ℓE} →
    EnrichedFunctor C D → EnrichedFunctor D E → EnrichedFunctor C E
  eseq  F G .F-ob c = F-ob G (F-ob F c)
  eseq  F G .F-hom = F-hom F V.⋆ F-hom G
  eseq  {C} F G .F-id =
    (sym (V.⋆Assoc _ _ _) ∙ cong (λ h → h V.⋆ F-hom G) (F .F-id) ) ∙ G .F-id
  eseq  {C} F G .F-seq =
    ((((cong₂ V._⋆_ (V.─⊗─ .F-seq _ _) refl ∙ V.⋆Assoc _ _ _ )
    ∙ cong (λ h → (F-hom F V.⊗ₕ F-hom F) V.⋆ h ) (G .F-seq))
    ∙ sym (V.⋆Assoc _ _ _))
    ∙ cong (λ h → h V.⋆ F-hom G) (F .F-seq))
    ∙ V.⋆Assoc _ _ _
