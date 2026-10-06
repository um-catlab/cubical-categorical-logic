{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Enrichment.LocallyContractive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation using (NatTrans)
open import Cubical.Categories.Monoidal.Base hiding (MonoidalStr)
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.NaturalTransformation.Base
  using (MonoidalNatTrans)
open import Cubical.Categories.Monoidal.Guarded
open import Cubical.Categories.Reasoning.Core
open import Cubical.Categories.Enriched.Enrichment.Base
import Cubical.Categories.Enriched.Enrichment.Functor.Base as FE
import Cubical.Categories.Enriched.BaseChange.Base as EnrBC
open import Cubical.Categories.Enriched.Enrichment.Instances.Underlying
open import Cubical.Categories.Enriched.Enrichment.Guarded
open import Cubical.Categories.Monoidal.Properties using (ρ⟨unit⟩≡η⟨unit⟩)
open import Cubical.Categories.NaturalTransformation using (symNatIso ; NatIso)
open import Cubical.Categories.Monoidal.Closed
import Cubical.Categories.Enriched.Enrichment.Instances.Self as Self

open FE using (EnrichmentFor)
open Functor

private
  variable
    ℓV ℓV' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _ {V : MonoidalCategory ℓV ℓV'} (G : GuardedModel V) where
  private
    module V = MonoidalCategory V
    open GuardedModel G
    module ▷L = LaxMonoidalFunctor ▷Lax
    module nextNT = MonoidalNatTrans next
  open Reasoning V.C

  module Later {C : Category ℓC ℓC'} (ℰC : Enrichment C V) where
    private
      module ℰC = Enrichment ℰC
      module C = Category C

    ▷EC : EnrichedCategory V ℓC
    ▷EC = EnrBC.BaseChange ▷Lax (toEnrichedCategory C V ℰC)

    ▷C : Category ℓC _
    ▷C = Γ*C-Cat ▷EC

    ▷ℰ : Enrichment ▷C V
    ▷ℰ = Underlying ▷EC

    next-seq : ∀ {X Y Z : C.ob} →
        (next⟦ ℰC.VE[ X , Y ] ⟧ V.⊗ₕ next⟦ ℰC.VE[ Y , Z ] ⟧) V.⋆
            EnrichedCategory.seq ▷EC X Y Z
      ≡ ℰC.seq X Y Z V.⋆ next⟦ ℰC.VE[ X , Z ] ⟧
    next-seq {X} {Y} {Z} =
      glue (nextNT.μ-law ℰC.VE[ X , Y ] ℰC.VE[ Y , Z ])
           (sym (nextNT.φ .NatTrans.N-hom (ℰC.seq X Y Z)))
      ∙ cong (V._⋆ next⟦ ℰC.VE[ X , Z ] ⟧) (V.⋆IdL _)

    nextF : Functor C ▷C
    nextF .Functor.F-ob x = x
    nextF .Functor.F-hom {x} {y} f = ℰC.⌜ f ⌝ V.⋆ next⟦ ℰC.VE[ x , y ] ⟧
    nextF .Functor.F-id {X} =
        cong (V._⋆ next⟦ ℰC.VE[ X , X ] ⟧) ℰC.⌜id⌝
      ∙ (cong (V._⋆ next⟦ ℰC.VE[ X , X ] ⟧) (sym (V.⋆IdL ℰC.id))
         ∙ glueTriL (nextNT.φ .NatTrans.N-hom ℰC.id) nextNT.ε-law)
      ∙ sym (V.⋆IdL _)
    nextF .Functor.F-seq {X} {Y} {Z} f g =
        cong (V._⋆ next⟦ ℰC.VE[ X , Z ] ⟧) (ℰC.⌜⋆⌝ f g)
      ∙ V.⋆Assoc _ _ _
      ∙ cong (V.η⁻¹⟨ V.unit ⟩ V.⋆_)
          (  V.⋆Assoc _ _ _
          ∙ cong ((ℰC.⌜ f ⌝ V.⊗ₕ ℰC.⌜ g ⌝) V.⋆_) (sym next-seq)
          ∙ sym (V.⋆Assoc _ _ _)
          ∙ cong (V._⋆ EnrichedCategory.seq ▷EC X Y Z)
              (sym (V.─⊗─ .Functor.F-seq
                      (ℰC.⌜ f ⌝ , ℰC.⌜ g ⌝)
                      (next⟦ ℰC.VE[ X , Y ] ⟧ , next⟦ ℰC.VE[ Y , Z ] ⟧)))
          )
      ∙ sym (V.⋆Assoc _ _ _)

    nextF-Enr : FE.Enrichment V ℰC ▷ℰ nextF
    nextF-Enr .FE.Enrichment.F[_,_] x y = next⟦ ℰC.VE[ x , y ] ⟧
    nextF-Enr .FE.Enrichment.F-id {X} =
      (cong (V._⋆ next⟦ ℰC.VE[ X , X ] ⟧) (sym (V.⋆IdL ℰC.id))
         ∙ glueTriL (nextNT.φ .NatTrans.N-hom ℰC.id) nextNT.ε-law)
    nextF-Enr .FE.Enrichment.F-seq {X} {Y} {Z} = next-seq
    nextF-Enr .FE.Enrichment.agree f = refl

  open Later using (▷ℰ)

  module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    {ℰC : Enrichment C V} {ℰD : Enrichment D V} {f : Category.ob C → Category.ob D}
    (F : EnrichmentFor V ℰC ℰD f) where
    private
      module F = EnrichmentFor F
      module ℰD = Enrichment ℰD

    ▷EnrFor : EnrichmentFor V (▷ℰ ℰC) (▷ℰ ℰD) f
    ▷EnrFor .EnrichmentFor.f[_,_] x y = ▷L.F-hom F.f[ x , y ]
    ▷EnrFor .EnrichmentFor.fid =
      V.⋆Assoc _ _ _
      ∙ cong (▷L.ε V.⋆_) (sym (▷L.F .F-seq _ _) ∙ cong ▷L.F-hom F.fid)
    ▷EnrFor .EnrichmentFor.f-seq {X} {Y} {Z} =
      sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ ▷L.F-hom (ℰD.seq (f X) (f Y) (f Z)))
          (▷L.μ .NatTrans.N-hom (F.f[ X , Y ] , F.f[ Y , Z ]))
      ∙ V.⋆Assoc _ _ _
      ∙ cong (▷L.μ⟨ _ , _ ⟩ V.⋆_)
          (sym (▷L.F .F-seq _ _) ∙ cong ▷L.F-hom F.f-seq ∙ ▷L.F .F-seq _ _)
      ∙ sym (V.⋆Assoc _ _ _)

  module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    (ℰC : Enrichment C V) (ℰD : Enrichment D V) (F : Functor C D) where
    private
      module ℰC = Enrichment ℰC
      module ℰD = Enrichment ℰD

    isLocallyContractive : Type _
    isLocallyContractive =
      Σ[ GE ∈ EnrichmentFor V (▷ℰ ℰC) ℰD (F .F-ob) ]
        (∀ {x y} (f : C [ x , y ]) →
          ℰD.⌜ F ⟪ f ⟫ ⌝ ≡ ℰC.⌜ f ⌝ V.⋆ (next⟦ ℰC.VE[ x , y ] ⟧ V.⋆ GE .EnrichmentFor.f[_,_] x y))

  module _ (cl : LeftClosed V) where
    private
      ℰ = Self.leftSelfEnrichment V cl
      module ℰ = Enrichment ℰ
      open LeftClosedNotation cl

    ▷-LC : isLocallyContractive ℰ ℰ ▷L.F
    ▷-LC .fst = Self.laxEnrichment V cl ▷Lax
    ▷-LC .snd {x} {y} f = ⟜-ext (ev-β (V.ρ⟨ ▷L.F-ob x ⟩ V.⋆ ▷L.F-hom f) ∙ sym (
        cong (λ m → (V.id V.⊗ₕ m) V.⋆ ev) (sym (V.⋆Assoc _ _ _))
      ∙ Self.ev-pre V cl _ (▷L.μ⟨ x , y ⟜ x ⟩ V.⋆ ▷L.F-hom ev)
      ∙ cong (λ m → (V.id V.⊗ₕ m) V.⋆ (▷L.μ⟨ x , y ⟜ x ⟩ V.⋆ ▷L.F-hom ev))
          (nextNT.φ .NatTrans.N-hom ℰ.⌜ f ⌝
           ∙ cong (V._⋆ ▷L.F-hom ℰ.⌜ f ⌝) (sym (V.⋆IdL _) ∙ nextNT.ε-law))
      ∙ Self.ε-pre V cl ▷Lax ℰ.⌜ f ⌝ ev f (ev-β (V.ρ⟨ x ⟩ V.⋆ f))))

  forgetAgree : {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    {ℰC : Enrichment C V} {ℰD : Enrichment D V} {F : Functor C D}
    → FE.Enrichment V ℰC ℰD F → EnrichmentFor V ℰC ℰD (F .F-ob)
  forgetAgree α .EnrichmentFor.f[_,_] = α .FE.Enrichment.F[_,_]
  forgetAgree α .EnrichmentFor.fid = α .FE.Enrichment.F-id
  forgetAgree α .EnrichmentFor.f-seq = α .FE.Enrichment.F-seq

  module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
    {ℰC : Enrichment C V} {ℰD : Enrichment D V} {ℰE : Enrichment E V}
    {F : Functor C D} {H : Functor D E}
    (lc : isLocallyContractive ℰC ℰD F) (ℋ : FE.Enrichment V ℰD ℰE H) where
    private
      module ℰC = Enrichment ℰC
      module ℰD = Enrichment ℰD
      module ℋ = FE.Enrichment ℋ
      GE = lc .fst

    LC-postcomp : isLocallyContractive ℰC ℰE (H ∘F F)
    LC-postcomp .fst = forgetAgree (ℋ FE.∘Enr EnrichmentFor.asEnrichment GE)
    LC-postcomp .snd {x} {y} f =
      ℋ.agree (F ⟪ f ⟫)
      ∙ cong (V._⋆ ℋ.F[ F ⟅ x ⟆ , F ⟅ y ⟆ ]) (lc .snd f)
      ∙ V.⋆Assoc _ _ _
      ∙ cong (ℰC.⌜ f ⌝ V.⋆_) (V.⋆Assoc _ _ _)

  module _ {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
    {ℰB : Enrichment B V} {ℰC : Enrichment C V} {ℰD : Enrichment D V}
    {H : Functor B C} {F : Functor C D}
    (ℋ : FE.Enrichment V ℰB ℰC H) (lc : isLocallyContractive ℰC ℰD F) where
    private
      module ℰB = Enrichment ℰB
      module ℰC = Enrichment ℰC
      module ℰD = Enrichment ℰD
      module ℋ = FE.Enrichment ℋ
      GE = lc .fst
      module GE = EnrichmentFor GE

    LC-precomp : isLocallyContractive ℰB ℰD (F ∘F H)
    LC-precomp .fst .EnrichmentFor.f[_,_] x y =
      ▷L.F-hom ℋ.F[ x , y ] V.⋆ GE.f[ H ⟅ x ⟆ , H ⟅ y ⟆ ]
    LC-precomp .fst .EnrichmentFor.fid {X} =
      sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ GE.f[ H ⟅ X ⟆ , H ⟅ X ⟆ ])
          (V.⋆Assoc _ _ _
           ∙ cong (▷L.ε V.⋆_) (sym (▷L.F-seq _ _) ∙ cong ▷L.F-hom ℋ.F-id))
      ∙ GE.fid
    LC-precomp .fst .EnrichmentFor.f-seq {X} {Y} {Z} =
      (▷L.F-hom ℋ.F[ X , Y ] V.⋆ GE.f[ _ , _ ]) V.⊗ₕ (▷L.F-hom ℋ.F[ Y , Z ] V.⋆ GE.f[ _ , _ ])
        V.⋆ ℰD.seq _ _ _
        ≡⟨ cong (V._⋆ ℰD.seq _ _ _) (V.─⊗─ .F-seq _ _) ∙ V.⋆Assoc _ _ _ ⟩
      (▷L.F-hom ℋ.F[ X , Y ] V.⊗ₕ ▷L.F-hom ℋ.F[ Y , Z ])
        V.⋆ ((GE.f[ _ , _ ] V.⊗ₕ GE.f[ _ , _ ]) V.⋆ ℰD.seq _ _ _)
        ≡⟨ cong ((▷L.F-hom ℋ.F[ X , Y ] V.⊗ₕ ▷L.F-hom ℋ.F[ Y , Z ]) V.⋆_) GE.f-seq ⟩
      (▷L.F-hom ℋ.F[ X , Y ] V.⊗ₕ ▷L.F-hom ℋ.F[ Y , Z ])
        V.⋆ ((▷L.μ⟨ _ , _ ⟩ V.⋆ ▷L.F-hom (ℰC.seq _ _ _)) V.⋆ GE.f[ _ , _ ])
        ≡⟨ sym (V.⋆Assoc _ _ _) ∙ cong (V._⋆ GE.f[ _ , _ ]) (sym (V.⋆Assoc _ _ _)) ⟩
      (((▷L.F-hom ℋ.F[ X , Y ] V.⊗ₕ ▷L.F-hom ℋ.F[ Y , Z ]) V.⋆ ▷L.μ⟨ _ , _ ⟩)
        V.⋆ ▷L.F-hom (ℰC.seq _ _ _)) V.⋆ GE.f[ _ , _ ]
        ≡⟨ cong (λ m → (m V.⋆ ▷L.F-hom (ℰC.seq _ _ _)) V.⋆ GE.f[ _ , _ ])
             (▷L.μ .NatTrans.N-hom (ℋ.F[ X , Y ] , ℋ.F[ Y , Z ])) ⟩
      ((▷L.μ⟨ _ , _ ⟩ V.⋆ ▷L.F-hom (ℋ.F[ X , Y ] V.⊗ₕ ℋ.F[ Y , Z ]))
        V.⋆ ▷L.F-hom (ℰC.seq _ _ _)) V.⋆ GE.f[ _ , _ ]
        ≡⟨ cong (V._⋆ GE.f[ _ , _ ])
             (V.⋆Assoc _ _ _
              ∙ cong (▷L.μ⟨ _ , _ ⟩ V.⋆_)
                  (sym (▷L.F-seq _ _) ∙ cong ▷L.F-hom ℋ.F-seq ∙ ▷L.F-seq _ _)
              ∙ sym (V.⋆Assoc _ _ _)) ⟩
      ((▷L.μ⟨ _ , _ ⟩ V.⋆ ▷L.F-hom (ℰB.seq X Y Z)) V.⋆ ▷L.F-hom ℋ.F[ X , Z ])
        V.⋆ GE.f[ _ , _ ]
        ≡⟨ V.⋆Assoc _ _ _ ⟩
      (▷L.μ⟨ _ , _ ⟩ V.⋆ ▷L.F-hom (ℰB.seq X Y Z))
        V.⋆ (▷L.F-hom ℋ.F[ X , Z ] V.⋆ GE.f[ _ , _ ]) ∎
    LC-precomp .snd {x} {y} f =
      lc .snd (H ⟪ f ⟫)
      ∙ cong (V._⋆ (next⟦ ℰC.VE[ H ⟅ x ⟆ , H ⟅ y ⟆ ] ⟧ V.⋆ GE.f[ _ , _ ])) (ℋ.agree f)
      ∙ V.⋆Assoc _ _ _
      ∙ cong (ℰB.⌜ f ⌝ V.⋆_)
          (sym (V.⋆Assoc _ _ _)
           ∙ cong (V._⋆ GE.f[ _ , _ ]) (nextNT.φ .NatTrans.N-hom ℋ.F[ x , y ])
           ∙ V.⋆Assoc _ _ _)

  private
    ρ⁻¹≡η⁻¹ : V.ρ⁻¹⟨ V.unit ⟩ ≡ V.η⁻¹⟨ V.unit ⟩
    ρ⁻¹≡η⁻¹ =
      sym (V.⋆IdR _)
      ∙ cong (V.ρ⁻¹⟨ V.unit ⟩ V.⋆_) (sym (V.η .NatIso.nIso V.unit .isIso.ret))
      ∙ sym (V.⋆Assoc _ _ _)
      ∙ cong (λ m → (V.ρ⁻¹⟨ V.unit ⟩ V.⋆ m) V.⋆ V.η⁻¹⟨ V.unit ⟩) (sym (ρ⟨unit⟩≡η⟨unit⟩ V))
      ∙ cong (V._⋆ V.η⁻¹⟨ V.unit ⟩) (V.ρ .NatIso.nIso V.unit .isIso.sec)
      ∙ V.⋆IdL _

  module Hylo {C : Category ℓC ℓC'} {ℰC : Enrichment C V} {F : Functor C C}
    (lc : isLocallyContractive ℰC ℰC F)
    {X B : Category.ob C} (c : C [ X , F ⟅ X ⟆ ]) (a : C [ F ⟅ B ⟆ , B ]) where
    private
      module C = Category C
      module ℰC = Enrichment ℰC
      GE = lc .fst
      module GE = EnrichmentFor GE

    preC : V.Hom[ ℰC.VE[ F ⟅ X ⟆ , F ⟅ B ⟆ ] , ℰC.VE[ X , F ⟅ B ⟆ ] ]
    preC = V.η⁻¹⟨ _ ⟩ V.⋆ ((ℰC.⌜ c ⌝ V.⊗ₕ V.id) V.⋆ ℰC.seq _ _ _)

    postC : V.Hom[ ℰC.VE[ X , F ⟅ B ⟆ ] , ℰC.VE[ X , B ] ]
    postC = V.ρ⁻¹⟨ _ ⟩ V.⋆ ((V.id V.⊗ₕ ℰC.⌜ a ⌝) V.⋆ ℰC.seq _ _ _)

    step : V.Hom[ ▷F ℰC.VE[ X , B ] , ℰC.VE[ X , B ] ]
    step = GE.f[ X , B ] V.⋆ (preC V.⋆ postC)

    pre-β : ∀ (k : C [ F ⟅ X ⟆ , F ⟅ B ⟆ ]) → ℰC.⌜ k ⌝ V.⋆ preC ≡ ℰC.⌜ c C.⋆ k ⌝
    pre-β k =
      sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ ((ℰC.⌜ c ⌝ V.⊗ₕ V.id) V.⋆ ℰC.seq _ _ _))
          (symNatIso V.η .NatIso.trans .NatTrans.N-hom ℰC.⌜ k ⌝)
      ∙ V.⋆Assoc _ _ _
      ∙ cong (V.η⁻¹⟨ V.unit ⟩ V.⋆_)
          (sym (V.⋆Assoc _ _ _)
           ∙ cong (V._⋆ ℰC.seq _ _ _)
               (sym (V.─⊗─ .F-seq _ _) ∙ cong₂ V._⊗ₕ_ (V.⋆IdL _) (V.⋆IdR _)))
      ∙ sym (ℰC.⌜⋆⌝ c k)

    post-β : ∀ (k : C [ X , F ⟅ B ⟆ ]) → ℰC.⌜ k ⌝ V.⋆ postC ≡ ℰC.⌜ k C.⋆ a ⌝
    post-β k =
      sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ ((V.id V.⊗ₕ ℰC.⌜ a ⌝) V.⋆ ℰC.seq _ _ _))
          (symNatIso V.ρ .NatIso.trans .NatTrans.N-hom ℰC.⌜ k ⌝)
      ∙ V.⋆Assoc _ _ _
      ∙ cong₂ V._⋆_ ρ⁻¹≡η⁻¹
          (sym (V.⋆Assoc _ _ _)
           ∙ cong (V._⋆ ℰC.seq _ _ _)
               (sym (V.─⊗─ .F-seq _ _) ∙ cong₂ V._⊗ₕ_ (V.⋆IdR _) (V.⋆IdL _)))
      ∙ sym (ℰC.⌜⋆⌝ k a)

    step-β : ∀ (h : C [ X , B ])
      → (ℰC.⌜ h ⌝ V.⋆ next⟦ ℰC.VE[ X , B ] ⟧) V.⋆ step ≡ ℰC.⌜ c C.⋆ (F ⟪ h ⟫ C.⋆ a) ⌝
    step-β h =
      sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ (preC V.⋆ postC))
          (V.⋆Assoc _ _ _ ∙ sym (lc .snd h))
      ∙ sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ postC) (pre-β (F ⟪ h ⟫))
      ∙ post-β (c C.⋆ F ⟪ h ⟫)
      ∙ cong ℰC.⌜_⌝ (C.⋆Assoc _ _ _)

    hylo : C [ X , B ]
    hylo = EnrichedLöb.löb G ℰC step

    hylo-eq : hylo ≡ c C.⋆ (F ⟪ hylo ⟫ C.⋆ a)
    hylo-eq =
      sym (ℰC.⇄-agree→ hylo)
      ∙ cong ℰC.⌞_⌟ (EnrichedLöb.löb-fix G ℰC step ∙ step-β hylo)
      ∙ ℰC.⇄-agree→ _

    hylo-uniq : (h : C [ X , B ]) → h ≡ c C.⋆ (F ⟪ h ⟫ C.⋆ a) → h ≡ hylo
    hylo-uniq h p =
      EnrichedLöb.löb-uniq G ℰC step h (cong ℰC.⌜_⌝ p ∙ sym (step-β h))
