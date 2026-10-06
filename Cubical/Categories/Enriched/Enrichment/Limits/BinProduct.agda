{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Enrichment.Limits.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Limits.Terminal using (isTerminal)
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Constructions.Reindex
  using (becomesUniversal ; becomesUniversal→UniversalElement)
open import Cubical.Categories.Reasoning.Core
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.HomFunctor
open import Cubical.Categories.Enriched.Enrichment.UniversalElement
import Cubical.Categories.Enriched.Enrichment.Functor.Base as FE

private
  variable
    ℓV ℓV' ℓC ℓC' : Level

open Functor
open NatTrans

module _ {V : MonoidalCategory ℓV ℓV'} {C : Category ℓC ℓC'} (ℰ : Enrichment C V) where
  private
    module V = MonoidalCategory V
    module C = Category C
    module ℰ = Enrichment ℰ
  open Reasoning V.C
  open import Cubical.Categories.Monoidal.Reasoning V

  EnrichedBinProduct : (X Y : C.ob) → Type _
  EnrichedBinProduct X Y = EnrichedUniversalElement ℰ
    (λ W → BinProductProf V.C ⟅ ℰ.VE[ W , X ] , ℰ.VE[ W , Y ] ⟆)
    (λ W → preservesBinProdCones (Hom[_,-] ℰ W) X Y)

  module _ (unit-terminal : isTerminal V.C V.unit)
    (Γ : C.ob) (G : Functor C C)
    (π₁ : NatTrans G (Constant C C Γ)) (π₂ : NatTrans G Id)
    (univ : ∀ X W → becomesUniversal (preservesBinProdCones (Hom[_,-] ℰ W) Γ X)
                      (G ⟅ X ⟆) (π₁ ⟦ X ⟧ , π₂ ⟦ X ⟧))
    where
    private
      module P (X W : C.ob) =
        BinProductNotation
          (becomesUniversal→UniversalElement (preservesBinProdCones (Hom[_,-] ℰ W) Γ X) (univ X W))

      ! : ∀ x → V.Hom[ x , V.unit ]
      ! x = unit-terminal x .fst

      !≡ : ∀ {x} (f g : V.Hom[ x , V.unit ]) → f ≡ g
      !≡ f g = isContr→isProp (unit-terminal _) f g

      F[_,_] : ∀ X Y → V.Hom[ ℰ.VE[ X , Y ] , ℰ.VE[ G ⟅ X ⟆ , G ⟅ Y ⟆ ] ]
      F[ X , Y ] = P._,p_ Y (G ⟅ X ⟆) (! _ V.⋆ ℰ.⌜ π₁ ⟦ X ⟧ ⌝) (Hom[-,_] ℰ Y ⟪ π₂ ⟦ X ⟧ ⟫)

      ⌜π₁⌝ : ∀ {X x} (k : V.Hom[ x , V.unit ]) (h : V.Hom[ x , ℰ.VE[ G ⟅ X ⟆ , Γ ] ])
        → h ≡ k V.⋆ ℰ.⌜ π₁ ⟦ X ⟧ ⌝ → h ≡ ! x V.⋆ ℰ.⌜ π₁ ⟦ X ⟧ ⌝
      ⌜π₁⌝ k h p = p ∙ cong (V._⋆ _) (!≡ k (! _))

      ⌜id⌝-post : ∀ {X Y} (f : C [ X , Y ]) → ℰ.id V.⋆ Hom[_,-] ℰ X ⟪ f ⟫ ≡ ℰ.⌜ f ⌝
      ⌜id⌝-post {X} f = cong (V._⋆ Hom[_,-] ℰ X ⟪ f ⟫) (sym ℰ.⌜id⌝) ∙ post-β ℰ C.id f ∙ cong ℰ.⌜_⌝ (C.⋆IdL f)

      ⌜id⌝-pre : ∀ {X Y} (f : C [ X , Y ]) → ℰ.id V.⋆ Hom[-,_] ℰ Y ⟪ f ⟫ ≡ ℰ.⌜ f ⌝
      ⌜id⌝-pre {Y = Y} f = cong (V._⋆ Hom[-,_] ℰ Y ⟪ f ⟫) (sym ℰ.⌜id⌝) ∙ pre-β ℰ C.id f ∙ cong ℰ.⌜_⌝ (C.⋆IdR f)

    ×-Enrichment : FE.Enrichment V ℰ ℰ G
    ×-Enrichment .FE.Enrichment.F[_,_] = F[_,_]
    ×-Enrichment .FE.Enrichment.F-id {X} = P.,p-extensionality X (G ⟅ X ⟆)
      ( V.⋆Assoc _ _ _
      ∙ cong (ℰ.id V.⋆_) (P.×β₁ X (G ⟅ X ⟆))
      ∙ sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ ℰ.⌜ π₁ ⟦ X ⟧ ⌝) (!≡ _ V.id)
      ∙ V.⋆IdL _
      ∙ sym (⌜id⌝-post (π₁ ⟦ X ⟧)))
      ( V.⋆Assoc _ _ _
      ∙ cong (ℰ.id V.⋆_) (P.×β₂ X (G ⟅ X ⟆))
      ∙ ⌜id⌝-pre (π₂ ⟦ X ⟧)
      ∙ sym (⌜id⌝-post (π₂ ⟦ X ⟧)))
    ×-Enrichment .FE.Enrichment.F-seq {X} {Y} {Z} =
      P.,p-extensionality Z (G ⟅ X ⟆) (lhs₁ ∙ sym rhs₁) (lhs₂ ∙ sym rhs₂)
      where
      FF = F[ X , Y ] V.⊗ₕ F[ Y , Z ]
      seqG = ℰ.seq (G ⟅ X ⟆) (G ⟅ Y ⟆) (G ⟅ Z ⟆)

      rhs₁ : (ℰ.seq X Y Z V.⋆ F[ X , Z ]) V.⋆ Hom[_,-] ℰ (G ⟅ X ⟆) ⟪ π₁ ⟦ Z ⟧ ⟫
        ≡ ! _ V.⋆ ℰ.⌜ π₁ ⟦ X ⟧ ⌝
      rhs₁ = ⌜π₁⌝ (ℰ.seq X Y Z V.⋆ ! _) _
        ( V.⋆Assoc _ _ _
        ∙ cong (ℰ.seq X Y Z V.⋆_) (P.×β₁ Z (G ⟅ X ⟆))
        ∙ sym (V.⋆Assoc _ _ _))

      lhs₁ : (FF V.⋆ seqG) V.⋆ Hom[_,-] ℰ (G ⟅ X ⟆) ⟪ π₁ ⟦ Z ⟧ ⟫ ≡ ! _ V.⋆ ℰ.⌜ π₁ ⟦ X ⟧ ⌝
      lhs₁ = ⌜π₁⌝ ((V.id V.⊗ₕ ! _) V.⋆ (V.ρ⟨ _ ⟩ V.⋆ ! _)) _
        ( V.⋆Assoc _ _ _
        ∙ cong (FF V.⋆_) (seq-post ℰ (π₁ ⟦ Z ⟧))
        ∙ pullˡ (merge₂ʳ ∙ cong (F[ X , Y ] V.⊗ₕ_) (P.×β₁ Z (G ⟅ Y ⟆)))
        ∙ cong (V._⋆ ℰ.seq _ _ _) split₂ʳ
        ∙ V.⋆Assoc _ _ _
        ∙ cong ((F[ X , Y ] V.⊗ₕ ! _) V.⋆_)
            (sym (pullˡ (V.ρ .NatIso.nIso _ .isIso.ret) ∙ V.⋆IdL _))
        ∙ sym (V.⋆Assoc _ _ _)
        ∙ cong (V._⋆ Hom[_,-] ℰ (G ⟅ X ⟆) ⟪ π₁ ⟦ Y ⟧ ⟫)
            ( cong (V._⋆ V.ρ⟨ _ ⟩) serialize₂₁
            ∙ V.⋆Assoc _ _ _
            ∙ cong ((V.id V.⊗ₕ ! _) V.⋆_) (V.ρ .NatIso.trans .N-hom F[ X , Y ]))
        ∙ V.⋆Assoc _ _ _
        ∙ cong ((V.id V.⊗ₕ ! _) V.⋆_)
            (V.⋆Assoc _ _ _ ∙ cong (V.ρ⟨ _ ⟩ V.⋆_) (P.×β₁ Y (G ⟅ X ⟆)))
        ∙ cong ((V.id V.⊗ₕ ! _) V.⋆_) (sym (V.⋆Assoc _ _ _))
        ∙ sym (V.⋆Assoc _ _ _))

      rhs₂ : (ℰ.seq X Y Z V.⋆ F[ X , Z ]) V.⋆ Hom[_,-] ℰ (G ⟅ X ⟆) ⟪ π₂ ⟦ Z ⟧ ⟫
        ≡ ℰ.seq X Y Z V.⋆ Hom[-,_] ℰ Z ⟪ π₂ ⟦ X ⟧ ⟫
      rhs₂ = V.⋆Assoc _ _ _ ∙ cong (ℰ.seq X Y Z V.⋆_) (P.×β₂ Z (G ⟅ X ⟆))

      lhs₂ : (FF V.⋆ seqG) V.⋆ Hom[_,-] ℰ (G ⟅ X ⟆) ⟪ π₂ ⟦ Z ⟧ ⟫
        ≡ ℰ.seq X Y Z V.⋆ Hom[-,_] ℰ Z ⟪ π₂ ⟦ X ⟧ ⟫
      lhs₂ =
          V.⋆Assoc _ _ _
        ∙ cong (FF V.⋆_) (seq-post ℰ (π₂ ⟦ Z ⟧))
        ∙ pullˡ (merge₂ʳ ∙ cong (F[ X , Y ] V.⊗ₕ_) (P.×β₂ Z (G ⟅ Y ⟆)))
        ∙ cong (V._⋆ ℰ.seq _ _ _) serialize₁₂
        ∙ V.⋆Assoc _ _ _
        ∙ cong ((F[ X , Y ] V.⊗ₕ V.id) V.⋆_) (seq-extranatural ℰ (π₂ ⟦ Y ⟧))
        ∙ pullˡ (merge₁ˡ ∙ cong (V._⊗ₕ V.id) (P.×β₂ Y (G ⟅ X ⟆)))
        ∙ sym (seq-pre ℰ (π₂ ⟦ X ⟧))
    ×-Enrichment .FE.Enrichment.agree {X} {Y} f = P.,p-extensionality Y (G ⟅ X ⟆)
      ( post-β ℰ (G ⟪ f ⟫) (π₁ ⟦ Y ⟧)
      ∙ cong ℰ.⌜_⌝ (π₁ .N-hom f ∙ C.⋆IdR _)
      ∙ sym (V.⋆Assoc _ _ _ ∙ cong (ℰ.⌜ f ⌝ V.⋆_) (P.×β₁ Y (G ⟅ X ⟆))
             ∙ sym (V.⋆Assoc _ _ _) ∙ cong (V._⋆ _) (!≡ _ V.id) ∙ V.⋆IdL _))
      ( post-β ℰ (G ⟪ f ⟫) (π₂ ⟦ Y ⟧)
      ∙ cong ℰ.⌜_⌝ (π₂ .N-hom f)
      ∙ sym (V.⋆Assoc _ _ _ ∙ cong (ℰ.⌜ f ⌝ V.⋆_) (P.×β₂ Y (G ⟅ X ⟆)) ∙ pre-β ℰ f (π₂ ⟦ X ⟧)))
