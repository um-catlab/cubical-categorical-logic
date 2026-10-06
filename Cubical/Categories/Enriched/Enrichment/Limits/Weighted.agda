{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Enrichment.Limits.Weighted where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Closed
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex using (PshHet)
open import Cubical.Categories.Reasoning.Core
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.HomFunctor
open import Cubical.Categories.Enriched.Enrichment.UniversalElement

private
  variable
    ℓV ℓV' ℓC ℓC' ℓJ ℓJ' : Level

open Functor
open NatTrans

module _ {V : MonoidalCategory ℓV ℓV'} {C : Category ℓC ℓC'} (ℰ : Enrichment C V)
  {J : Category ℓJ ℓJ'} (w : Functor J (MonoidalCategory.C V)) (D : Functor J C) where
  private
    module V = MonoidalCategory V
    module C = Category C
    module ℰ = Enrichment ℰ
  open Reasoning V.C
  open import Cubical.Categories.Monoidal.Reasoning V

  WeightedCones : Presheaf C (ℓ-max (ℓ-max ℓJ ℓJ') ℓV')
  WeightedCones .F-ob W = NatTrans w (Hom[_,-] ℰ W ∘F D) , isSetNatTrans
  WeightedCones .F-hom f e .N-ob j = e ⟦ j ⟧ V.⋆ Hom[-,_] ℰ (D ⟅ j ⟆) ⟪ f ⟫
  WeightedCones .F-hom f e .N-hom {y = y} k =
      sym (V.⋆Assoc _ _ _)
    ∙ cong (V._⋆ Hom[-,_] ℰ (D ⟅ y ⟆) ⟪ f ⟫) (e .N-hom k)
    ∙ V.⋆Assoc _ _ _
    ∙ cong (e ⟦ _ ⟧ V.⋆_) (sym (pre-post ℰ f (D ⟪ k ⟫)))
    ∙ sym (V.⋆Assoc _ _ _)
  WeightedCones .F-id = funExt λ e → makeNatTransPath (funExt λ j →
    cong (e ⟦ j ⟧ V.⋆_) (Hom[-,_] ℰ _ .F-id) ∙ V.⋆IdR _)
  WeightedCones .F-seq f g = funExt λ e → makeNatTransPath (funExt λ j →
    cong (e ⟦ j ⟧ V.⋆_) (Hom[-,_] ℰ _ .F-seq f g) ∙ sym (V.⋆Assoc _ _ _))

  module _ (W : C.ob) where
    WeightedConesᴱ : Presheaf V.C (ℓ-max (ℓ-max ℓJ ℓJ') ℓV')
    WeightedConesᴱ .F-ob U = NatTrans (_⊗- V U ∘F w) (Hom[_,-] ℰ W ∘F D) , isSetNatTrans
    WeightedConesᴱ .F-hom u e .N-ob j = (u V.⊗ₕ V.id) V.⋆ e ⟦ j ⟧
    WeightedConesᴱ .F-hom u e .N-hom k =
        sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ e ⟦ _ ⟧) (sym serialize₂₁ ∙ serialize₁₂)
      ∙ V.⋆Assoc _ _ _
      ∙ cong ((u V.⊗ₕ V.id) V.⋆_) (e .N-hom k)
      ∙ sym (V.⋆Assoc _ _ _)
    WeightedConesᴱ .F-id = funExt λ e → makeNatTransPath (funExt λ j →
      cong (V._⋆ e ⟦ j ⟧) ⊗-id ∙ V.⋆IdL _)
    WeightedConesᴱ .F-seq u u' = funExt λ e → makeNatTransPath (funExt λ j →
      cong (V._⋆ e ⟦ j ⟧) (cong ((u' V.⋆ u) V.⊗ₕ_) (sym (V.⋆IdL V.id)) ∙ ⊗-distrib-over-⋆)
      ∙ V.⋆Assoc _ _ _)

    preservesWeightedCones : PshHet (Hom[_,-] ℰ W) WeightedCones WeightedConesᴱ
    preservesWeightedCones .PshHom.N-ob L e .N-ob j = (V.id V.⊗ₕ e ⟦ j ⟧) V.⋆ ℰ.seq W L (D ⟅ j ⟆)
    preservesWeightedCones .PshHom.N-ob L e .N-hom k =
        sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ ℰ.seq _ _ _)
          (sym (V.─⊗─ .F-seq _ _) ∙ cong₂ V._⊗ₕ_ (V.⋆IdL _) (e .N-hom k) ∙ split₂ʳ)
      ∙ V.⋆Assoc _ _ _
      ∙ cong ((V.id V.⊗ₕ e ⟦ _ ⟧) V.⋆_) (sym (seq-post ℰ (D ⟪ k ⟫)))
      ∙ sym (V.⋆Assoc _ _ _)
    preservesWeightedCones .PshHom.N-hom L' L f e = makeNatTransPath (funExt λ j →
        cong (V._⋆ ℰ.seq W L' (D ⟅ j ⟆)) split₂ʳ
      ∙ V.⋆Assoc _ _ _
      ∙ cong ((V.id V.⊗ₕ e ⟦ j ⟧) V.⋆_) (seq-extranatural ℰ f)
      ∙ sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ ℰ.seq W L (D ⟅ j ⟆)) (sym serialize₂₁ ∙ serialize₁₂)
      ∙ V.⋆Assoc _ _ _)

  EnrichedWeightedLimit : Type _
  EnrichedWeightedLimit = EnrichedUniversalElement ℰ WeightedConesᴱ preservesWeightedCones
