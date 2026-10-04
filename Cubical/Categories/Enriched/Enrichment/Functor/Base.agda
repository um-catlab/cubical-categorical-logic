-- Enrichment of functors, following "Univalent Enriched Categories and the Enriched Rezk Completion" (v.d. Weide 2026)
module Cubical.Categories.Enriched.Enrichment.Functor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Enriched.Enrichment.Base renaming (Enrichment to VE)
open import Cubical.Foundations.Isomorphism
import Cubical.Categories.Monoidal.Reasoning as MonRes

record Enrichment
  {ℓV ℓV' ℓC ℓC' ℓD ℓD' : Level}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (V : MonoidalCategory ℓV ℓV')
  (ℰC : VE C V)
  (ℰD : VE D V)
  (F : Functor C D) : Type (ℓ-max (ℓ-max ℓV ℓV') (ℓ-max ℓC ℓC')) where
   private
     module C = Category C
     module D = Category D
     module V = MonoidalCategory V
     module ℰD = VE ℰD
     module ℰC = VE ℰC
     open VE ℰC renaming (VE[_,_] to ℰC[_,_])
     open VE ℰD renaming (VE[_,_] to ℰD[_,_])
   open Functor F

   field
      F[_,_] : ∀ x y → V.Hom[ ℰC[ x , y ] , ℰD[ F-ob x , F-ob y ] ]
      F-id : {X : C.ob} → (ℰC.id {X} V.⋆  F[ X , X ]) ≡ ℰD.id {F-ob X}
      F-seq : {X Y Z : C.ob} →
        (F[ X , Y ] V.⊗ₕ F[ Y , Z ]) V.⋆ ℰD.seq (F-ob X) (F-ob Y) (F-ob Z)
        ≡
        ℰC.seq X Y Z V.⋆ F[ X , Z ]
      agree : ∀ {x y} → ∀ (f : C.Hom[ x , y ]) →
        ℰD.⌜ F-hom f ⌝ ≡ ℰC.⌜ f ⌝ V.⋆ F[ x , y ]

record EnrichmentFor
  {ℓV ℓV' ℓC ℓC' ℓD ℓD' : Level}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (V : MonoidalCategory ℓV ℓV')
  (ℰC : VE C V)
  (ℰD : VE D V)
  (F-ob : Category.ob C → Category.ob D) : Type (ℓ-max ℓC ℓV')
  where
    private
      module C = Category C
      module D = Category D
      module V = MonoidalCategory V
      module ℰD = VE ℰD
      module ℰC = VE ℰC
      open VE ℰC renaming (VE[_,_] to ℰC[_,_])
      open VE ℰD renaming (VE[_,_] to ℰD[_,_])

    field
      f[_,_] : ∀ x y → V.Hom[ ℰC[ x , y ] , ℰD[ F-ob x , F-ob y ] ]
      fid : {X : C.ob} → (ℰC.id {X} V.⋆  f[ X , X ]) ≡ ℰD.id {F-ob X}
      f-seq : {X Y Z : C.ob} →
        (f[ X , Y ] V.⊗ₕ f[ Y , Z ]) V.⋆ ℰD.seq (F-ob X) (F-ob Y) (F-ob Z)
        ≡
        ℰC.seq X Y Z V.⋆ f[ X , Z ]
           
    UF : Functor C D
    UF .Functor.F-ob = F-ob
    UF .Functor.F-hom f =  ℰD.⌞ ℰC.⌜ f ⌝ V.⋆ f[ _ , _ ] ⌟
    UF .Functor.F-id {X} =
        cong (λ h → ℰD.⌞ h V.⋆ f[ X , X ] ⌟) ℰC.⌜id⌝
      ∙ cong ℰD.⌞_⌟ (fid ∙ sym ℰD.⌜id⌝)
      ∙ ℰD.⇄-agree→ _
    UF .Functor.F-seq {X}{Y}{Z} f g = -- TODO is this the simplest way?
      cong ℰD.⌞_⌟ bigEq ∙ ℰD.⇄-agree→ _
      where
        open MonRes V using (⊗-distrib-over-⋆)
        bigEq :
            ℰC.⌜ (C Category.⋆ f) g ⌝ V.⋆ f[ X , Z ]
          ≡ ℰD.⌜ ℰD.⌞ ℰC.⌜ f ⌝ V.⋆ f[ X , Y ] ⌟ D.⋆
                 ℰD.⌞ ℰC.⌜ g ⌝ V.⋆ f[ Y , Z ] ⌟ ⌝
        bigEq =
            cong (V._⋆ f[ X , Z ]) (ℰC.⌜⋆⌝ f g)
          ∙ V.⋆Assoc _ _ _
          ∙ cong (V.η⁻¹⟨ _ ⟩ V.⋆_) (V.⋆Assoc _ _ _)
          ∙ cong (λ z → V.η⁻¹⟨ _ ⟩ V.⋆ ((ℰC.⌜ f ⌝ V.⊗ₕ ℰC.⌜ g ⌝) V.⋆ z))
                 (sym f-seq)
          ∙ cong (V.η⁻¹⟨ _ ⟩ V.⋆_) (sym (V.⋆Assoc _ _ _))
          ∙ cong (λ z → V.η⁻¹⟨ _ ⟩ V.⋆ (z V.⋆ ℰD.seq _ _ _))
                 (sym ⊗-distrib-over-⋆)
          ∙ cong₂ (λ p q → V.η⁻¹⟨ _ ⟩ V.⋆ ((p V.⊗ₕ q) V.⋆ ℰD.seq _ _ _))
                  (sym (ℰD.⇄-agree← _)) (sym (ℰD.⇄-agree← _))
          ∙ sym (ℰD.⌜⋆⌝ _ _)
     
    asEnrichment : Enrichment V ℰC ℰD UF
    asEnrichment .Enrichment.F[_,_] = f[_,_]
    asEnrichment .Enrichment.F-id = fid
    asEnrichment .Enrichment.F-seq = f-seq
    asEnrichment .Enrichment.agree f = ℰD.⇄-agree← _
     

------------------------------------------------------------------------
-- Composition of enriched functors: given α : ℰC → ℰD along F and
-- β : ℰD → ℰE along G, the composite has underlying functor G ∘F F and
-- strength at (x, y) equal to α.F[x, y] ⋆ β.F[Fx, Fy].
module _
  {ℓV ℓV' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  {V : MonoidalCategory ℓV ℓV'}
  {ℰC : VE C V} {ℰD : VE D V} {ℰE : VE E V}
  {F : Functor C D} {G : Functor D E}
  (β : Enrichment V ℰD ℰE G)
  (α : Enrichment V ℰC ℰD F)
  where
  private
    module V = MonoidalCategory V
    module ℰC = VE ℰC
    module ℰD = VE ℰD
    module ℰE = VE ℰE
    module α = Enrichment α
    module β = Enrichment β
    module F = Functor F
    module G = Functor G
    open MonRes V

  _∘Enr_ : Enrichment V ℰC ℰE (G ∘F F)
  _∘Enr_ .Enrichment.F[_,_] x y =
    α.F[ x , y ] V.⋆ β.F[ F.F-ob x , F.F-ob y ]
  _∘Enr_ .Enrichment.F-id {X} =
      sym (V.⋆Assoc _ _ _)
    ∙ cong (V._⋆ β.F[ F.F-ob X , F.F-ob X ]) α.F-id
    ∙ β.F-id
  _∘Enr_ .Enrichment.F-seq {X}{Y}{Z} =
      cong (V._⋆ ℰE.seq _ _ _) ⊗-distrib-over-⋆
    ∙ V.⋆Assoc _ _ _
    ∙ cong ((α.F[ X , Y ] V.⊗ₕ α.F[ Y , Z ]) V.⋆_) β.F-seq
    ∙ sym (V.⋆Assoc _ _ _)
    ∙ cong (V._⋆ β.F[ F.F-ob X , F.F-ob Z ]) α.F-seq
    ∙ V.⋆Assoc _ _ _
  _∘Enr_ .Enrichment.agree f =
      β.agree (F.F-hom f)
    ∙ cong (V._⋆ β.F[ _ , _ ]) (α.agree f)
    ∙ V.⋆Assoc _ _ _
