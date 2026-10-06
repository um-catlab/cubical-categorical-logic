{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Enrichment.Limits.Weighted.Construction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.TwistedArrow
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Reindex
  using (becomesUniversal→UniversalElement)
open import Cubical.Categories.Monoidal.Closed using (_⊗-)
open import Cubical.Categories.Limits.AsRepresentable
open import Cubical.Categories.Limits.Conical
open import Cubical.Categories.Reasoning.Core
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.HomFunctor hiding (post)
open import Cubical.Categories.Enriched.Enrichment.Limits.Power
open import Cubical.Categories.Enriched.Enrichment.Limits.Conical
open import Cubical.Categories.Enriched.Enrichment.Limits.Weighted

private
  variable
    ℓV ℓV' ℓC ℓC' ℓJ ℓJ' : Level

open Functor
open NatTrans

module _ {V : MonoidalCategory ℓV ℓV'} {C : Category ℓC ℓC'} (ℰ : Enrichment C V)
  (pws : ∀ v X → EnrichedPower ℰ v X)
  {J : Category ℓJ ℓJ'} (w : Functor J (MonoidalCategory.C V)) (D : Functor J C) where
  private
    module V = MonoidalCategory V
    module C = Category C
    module ℰ = Enrichment ℰ
    module J = Category J
    open Reasoning V.C
    Tw = TwistedArrowCategory J
    ⋔ = PowerF ℰ pws
    module pw (v : V.ob) (X : C.ob) = UniversalElementNotation (pws v X .fst)

    pre : ∀ {Y} {X X' : C.ob} → C [ X' , X ] → V.Hom[ ℰ.VE[ X , Y ] , ℰ.VE[ X' , Y ] ]
    pre {Y} f = Hom[-,_] ℰ Y ⟪ f ⟫


  E : Functor Tw C
  E = ⋔ ∘F ((w ^opF) ×F D) ∘F TwistedEnds J

  ev : ∀ j j' → V.Hom[ w ⟅ j ⟆ , ℰ.VE[ ⋔ ⟅ w ⟅ j ⟆ , D ⟅ j' ⟆ ⟆ , D ⟅ j' ⟆ ] ]
  ev j j' = pw.element (w ⟅ j ⟆) (D ⟅ j' ⟆)

  idTw : ∀ j → Tw .Category.ob
  idTw j = (j , j) , J.id

  left : ∀ {j j'} (g : J [ j , j' ]) → Tw [ idTw j , ((j , j') , g) ]
  left g = (J.id , g) , cong (J._⋆ g) (J.⋆IdL J.id) ∙ J.⋆IdL g

  right : ∀ {j j'} (g : J [ j , j' ]) → Tw [ idTw j' , ((j , j') , g) ]
  right g = (g , J.id) , J.⋆IdR _ ∙ J.⋆IdR g

  private
    post : ∀ {W} {X X' : C.ob} → C [ X , X' ] → V.Hom[ ℰ.VE[ W , X ] , ℰ.VE[ W , X' ] ]
    post {W} f = Hom[_,-] ℰ W ⟪ f ⟫

    powβ : ∀ {v v' X X'} (u : V.Hom[ v' , v ]) (f : C [ X , X' ])
      → pw.element v' X' V.⋆ pre (⋔ ⟪ u , f ⟫) ≡ u V.⋆ (pw.element v X V.⋆ post f)
    powβ {v' = v'} {X' = X'} u f = pw.β v' X'

  module _ {W : C.ob} (c : NatTrans (ΔCone ⟅ W ⟆) E) where
    private
      c-left : ∀ {j j'} (g : J [ j , j' ]) → c ⟦ idTw j ⟧ C.⋆ E ⟪ left g ⟫ ≡ c ⟦ (j , j') , g ⟧
      c-left g = sym (c .N-hom (left g)) ∙ C.⋆IdL _

      c-right : ∀ {j j'} (g : J [ j , j' ]) → c ⟦ idTw j' ⟧ C.⋆ E ⟪ right g ⟫ ≡ c ⟦ (j , j') , g ⟧
      c-right g = sym (c .N-hom (right g)) ∙ C.⋆IdL _

    cone→weighted-at : ∀ j → V.Hom[ w ⟅ j ⟆ , ℰ.VE[ W , D ⟅ j ⟆ ] ]
    cone→weighted-at j = ev j j V.⋆ pre (c ⟦ idTw j ⟧)

    at-post : ∀ {j j'} (g : J [ j , j' ])
      → cone→weighted-at j V.⋆ post (D ⟪ g ⟫) ≡ ev j j' V.⋆ pre (c ⟦ (j , j') , g ⟧)
    at-post {j} {j'} g =
        V.⋆Assoc _ _ _
      ∙ cong (ev j j V.⋆_) (pre-post ℰ (c ⟦ idTw j ⟧) (D ⟪ g ⟫))
      ∙ sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ pre (c ⟦ idTw j ⟧))
          (sym (V.⋆IdL _) ∙ cong (V._⋆ (ev j j V.⋆ post (D ⟪ g ⟫))) (sym (w .F-id))
           ∙ sym (powβ (w ⟪ J.id ⟫) (D ⟪ g ⟫)))
      ∙ V.⋆Assoc _ _ _
      ∙ cong (ev j j' V.⋆_) (sym (Hom[-,_] ℰ _ .F-seq _ _) ∙ cong pre (c-left g))

    pre-at : ∀ {j j'} (g : J [ j , j' ])
      → w ⟪ g ⟫ V.⋆ cone→weighted-at j' ≡ ev j j' V.⋆ pre (c ⟦ (j , j') , g ⟧)
    pre-at {j} {j'} g =
        sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ pre (c ⟦ idTw j' ⟧))
          (cong (w ⟪ g ⟫ V.⋆_)
             (sym (V.⋆IdR _) ∙ cong (ev j' j' V.⋆_) (sym (cong post (D .F-id) ∙ Hom[_,-] ℰ _ .F-id)))
           ∙ sym (powβ (w ⟪ g ⟫) (D ⟪ J.id ⟫)))
      ∙ V.⋆Assoc _ _ _
      ∙ cong (ev j j' V.⋆_) (sym (Hom[-,_] ℰ _ .F-seq _ _) ∙ cong pre (c-right g))

    cone→weighted : NatTrans w (Hom[_,-] ℰ W ∘F D)
    cone→weighted .N-ob = cone→weighted-at
    cone→weighted .N-hom g = pre-at g ∙ sym (at-post g)

  module _ {W : C.ob} (t : NatTrans w (Hom[_,-] ℰ W ∘F D)) where
    weighted→cone-at : ∀ x → C [ W , E ⟅ x ⟆ ]
    weighted→cone-at ((j , j') , g) = pw.intro (w ⟅ j ⟆) (D ⟅ j' ⟆) (t ⟦ j ⟧ V.⋆ post (D ⟪ g ⟫))

    private
      ev-intro : ∀ {j j'} (g : J [ j , j' ])
        → ev j j' V.⋆ pre (weighted→cone-at ((j , j') , g)) ≡ t ⟦ j ⟧ V.⋆ post (D ⟪ g ⟫)
      ev-intro {j} {j'} g = pw.β (w ⟅ j ⟆) (D ⟅ j' ⟆)

    weighted→cone : NatTrans (ΔCone ⟅ W ⟆) E
    weighted→cone .N-ob = weighted→cone-at
    weighted→cone .N-hom {(j , j') , g} {(k , k') , h} ((u , v) , p) =
      C.⋆IdL _ ∙ pw.extensionality (w ⟅ k ⟆) (D ⟅ k' ⟆) (sym (
        ev k k' V.⋆ pre (weighted→cone-at ((j , j') , g) C.⋆ ⋔ ⟪ w ⟪ u ⟫ , D ⟪ v ⟫ ⟫)
          ≡⟨ cong (ev k k' V.⋆_) (Hom[-,_] ℰ _ .F-seq _ _) ∙ sym (V.⋆Assoc _ _ _) ⟩
        (ev k k' V.⋆ pre (⋔ ⟪ w ⟪ u ⟫ , D ⟪ v ⟫ ⟫)) V.⋆ pre (weighted→cone-at ((j , j') , g))
          ≡⟨ cong (V._⋆ pre (weighted→cone-at ((j , j') , g))) (powβ (w ⟪ u ⟫) (D ⟪ v ⟫)) ⟩
        (w ⟪ u ⟫ V.⋆ (ev j j' V.⋆ post (D ⟪ v ⟫))) V.⋆ pre (weighted→cone-at ((j , j') , g))
          ≡⟨ V.⋆Assoc _ _ _ ∙ cong (w ⟪ u ⟫ V.⋆_)
               (V.⋆Assoc _ _ _
               ∙ cong (ev j j' V.⋆_) (sym (pre-post ℰ (weighted→cone-at ((j , j') , g)) (D ⟪ v ⟫)))
               ∙ sym (V.⋆Assoc _ _ _)
               ∙ cong (V._⋆ post (D ⟪ v ⟫)) (ev-intro g)) ⟩
        w ⟪ u ⟫ V.⋆ ((t ⟦ j ⟧ V.⋆ post (D ⟪ g ⟫)) V.⋆ post (D ⟪ v ⟫))
          ≡⟨ sym (V.⋆Assoc _ _ _) ∙ cong (V._⋆ post (D ⟪ v ⟫)) (sym (V.⋆Assoc _ _ _)) ⟩
        ((w ⟪ u ⟫ V.⋆ t ⟦ j ⟧) V.⋆ post (D ⟪ g ⟫)) V.⋆ post (D ⟪ v ⟫)
          ≡⟨ cong (λ m → (m V.⋆ post (D ⟪ g ⟫)) V.⋆ post (D ⟪ v ⟫)) (t .N-hom u) ⟩
        ((t ⟦ k ⟧ V.⋆ post (D ⟪ u ⟫)) V.⋆ post (D ⟪ g ⟫)) V.⋆ post (D ⟪ v ⟫)
          ≡⟨ V.⋆Assoc _ _ _ ∙ V.⋆Assoc _ _ _
           ∙ cong (t ⟦ k ⟧ V.⋆_)
               (cong (post (D ⟪ u ⟫) V.⋆_) (sym (Hom[_,-] ℰ W .F-seq _ _))
               ∙ sym (Hom[_,-] ℰ W .F-seq _ _)
               ∙ cong post (cong (D ⟪ u ⟫ C.⋆_) (sym (D .F-seq g v)) ∙ sym (D .F-seq u (g J.⋆ v))
                            ∙ cong (D ⟪_⟫) (sym (J.⋆Assoc u g v) ∙ p))) ⟩
        t ⟦ k ⟧ V.⋆ post (D ⟪ h ⟫)
          ≡⟨ sym (ev-intro h) ⟩
        ev k k' V.⋆ pre (weighted→cone-at ((k , k') , h)) ∎))

  Cones≅WeightedCones : PshIso (Cones E) (WeightedCones ℰ w D)
  Cones≅WeightedCones .PshIso.trans .PshHom.N-ob W = cone→weighted
  Cones≅WeightedCones .PshIso.trans .PshHom.N-hom W' W f c = makeNatTransPath (funExt λ j →
    cong (ev j j V.⋆_) (Hom[-,_] ℰ _ .F-seq _ _) ∙ sym (V.⋆Assoc _ _ _))
  Cones≅WeightedCones .PshIso.nIso W .fst = weighted→cone
  Cones≅WeightedCones .PshIso.nIso W .snd .fst t = makeNatTransPath (funExt λ j →
    pw.β (w ⟅ j ⟆) (D ⟅ j ⟆)
    ∙ cong (t ⟦ j ⟧ V.⋆_) (cong post (D .F-id) ∙ Hom[_,-] ℰ W .F-id)
    ∙ V.⋆IdR _)
  Cones≅WeightedCones .PshIso.nIso W .snd .snd c = makeNatTransPath (funExt λ ((j , j') , g) →
    cong (pw.intro (w ⟅ j ⟆) (D ⟅ j' ⟆)) (at-post c g)
    ∙ sym (pw.η (w ⟅ j ⟆) (D ⟅ j' ⟆)))

  limit→WeightedLimit : limit E → UniversalElement C (WeightedCones ℰ w D)
  limit→WeightedLimit lim = lim ◁PshIso Cones≅WeightedCones

  module _ (W : C.ob) where
    private
      open import Cubical.Categories.Monoidal.Reasoning V
      module pwᴱ (v : V.ob) (X : C.ob) = UniversalElementNotation
        (becomesUniversal→UniversalElement (preservesPowerCones ℰ v X W) (pws v X .snd W))

      evᴱ : ∀ j j' → V.Hom[ ℰ.VE[ W , ⋔ ⟅ w ⟅ j ⟆ , D ⟅ j' ⟆ ⟆ ] V.⊗ w ⟅ j ⟆ , ℰ.VE[ W , D ⟅ j' ⟆ ] ]
      evᴱ j j' = pwᴱ.element (w ⟅ j ⟆) (D ⟅ j' ⟆)

      powβᴱ : ∀ {v v' X X'} (u : V.Hom[ v' , v ]) (f : C [ X , X' ])
        → (post (⋔ ⟪ u , f ⟫) V.⊗ₕ V.id) V.⋆ pwᴱ.element v' X'
          ≡ (V.id V.⊗ₕ u) V.⋆ (pwᴱ.element v X V.⋆ post f)
      powβᴱ {v} {v'} {X} {X'} u f =
          sym (preservesPowerCones ℰ v' X' W .PshHom.N-hom _ _ (⋔ ⟪ u , f ⟫) (pw.element v' X'))
        ∙ cong (λ m → (V.id V.⊗ₕ m) V.⋆ ℰ.seq W _ X') (powβ u f)
        ∙ cong (V._⋆ ℰ.seq W _ X') (split₂ʳ ∙ cong ((V.id V.⊗ₕ u) V.⋆_) split₂ʳ)
        ∙ V.⋆Assoc _ _ _
        ∙ cong ((V.id V.⊗ₕ u) V.⋆_)
            (V.⋆Assoc _ _ _
            ∙ cong ((V.id V.⊗ₕ pw.element v X) V.⋆_) (sym (seq-post ℰ f))
            ∙ sym (V.⋆Assoc _ _ _))

      ⊗id-seq : ∀ {a b c} (f : V.Hom[ a , b ]) (g : V.Hom[ b , c ]) {d}
        → ((f V.⋆ g) V.⊗ₕ V.id {d}) ≡ (f V.⊗ₕ V.id) V.⋆ (g V.⊗ₕ V.id)
      ⊗id-seq f g = cong ((f V.⋆ g) V.⊗ₕ_) (sym (V.⋆IdL _)) ∙ ⊗-distrib-over-⋆

    module _ {U : V.ob} (c : NatTrans (ΔCone ⟅ U ⟆) (Hom[_,-] ℰ W ∘F E)) where
      private
        c-left : ∀ {j j'} (g : J [ j , j' ])
          → c ⟦ idTw j ⟧ V.⋆ post (E ⟪ left g ⟫) ≡ c ⟦ (j , j') , g ⟧
        c-left g = sym (c .N-hom (left g)) ∙ V.⋆IdL _

        c-right : ∀ {j j'} (g : J [ j , j' ])
          → c ⟦ idTw j' ⟧ V.⋆ post (E ⟪ right g ⟫) ≡ c ⟦ (j , j') , g ⟧
        c-right g = sym (c .N-hom (right g)) ∙ V.⋆IdL _

      coneᴱ→weighted-at : ∀ j → V.Hom[ U V.⊗ w ⟅ j ⟆ , ℰ.VE[ W , D ⟅ j ⟆ ] ]
      coneᴱ→weighted-at j = (c ⟦ idTw j ⟧ V.⊗ₕ V.id) V.⋆ evᴱ j j

      at-postᴱ : ∀ {j j'} (g : J [ j , j' ])
        → coneᴱ→weighted-at j V.⋆ post (D ⟪ g ⟫) ≡ (c ⟦ (j , j') , g ⟧ V.⊗ₕ V.id) V.⋆ evᴱ j j'
      at-postᴱ {j} {j'} g =
          V.⋆Assoc _ _ _
        ∙ cong ((c ⟦ idTw j ⟧ V.⊗ₕ V.id) V.⋆_)
            ( sym (V.⋆IdL _)
            ∙ cong (V._⋆ (evᴱ j j V.⋆ post (D ⟪ g ⟫)))
                (sym (cong (V.id V.⊗ₕ_) (w .F-id) ∙ V.─⊗─ .F-id))
            ∙ sym (powβᴱ (w ⟪ J.id ⟫) (D ⟪ g ⟫)))
        ∙ sym (V.⋆Assoc _ _ _)
        ∙ cong (V._⋆ evᴱ j j') (sym (⊗id-seq _ _) ∙ cong (V._⊗ₕ V.id) (c-left g))

      pre-atᴱ : ∀ {j j'} (g : J [ j , j' ])
        → (V.id V.⊗ₕ w ⟪ g ⟫) V.⋆ coneᴱ→weighted-at j' ≡ (c ⟦ (j , j') , g ⟧ V.⊗ₕ V.id) V.⋆ evᴱ j j'
      pre-atᴱ {j} {j'} g =
          sym (V.⋆Assoc _ _ _)
        ∙ cong (V._⋆ evᴱ j' j') (sym serialize₂₁ ∙ serialize₁₂)
        ∙ V.⋆Assoc _ _ _
        ∙ cong ((c ⟦ idTw j' ⟧ V.⊗ₕ V.id) V.⋆_)
            ( cong ((V.id V.⊗ₕ w ⟪ g ⟫) V.⋆_)
                (sym (V.⋆IdR _) ∙ cong (evᴱ j' j' V.⋆_)
                  (sym (cong post (D .F-id) ∙ Hom[_,-] ℰ W .F-id)))
            ∙ sym (powβᴱ (w ⟪ g ⟫) (D ⟪ J.id ⟫)))
        ∙ sym (V.⋆Assoc _ _ _)
        ∙ cong (V._⋆ evᴱ j j') (sym (⊗id-seq _ _) ∙ cong (V._⊗ₕ V.id) (c-right g))

      coneᴱ→weighted : NatTrans (_⊗- V U ∘F w) (Hom[_,-] ℰ W ∘F D)
      coneᴱ→weighted .N-ob = coneᴱ→weighted-at
      coneᴱ→weighted .N-hom g = pre-atᴱ g ∙ sym (at-postᴱ g)

    module _ {U : V.ob} (t : NatTrans (_⊗- V U ∘F w) (Hom[_,-] ℰ W ∘F D)) where
      weightedᴱ→cone-at : ∀ x → V.Hom[ U , ℰ.VE[ W , E ⟅ x ⟆ ] ]
      weightedᴱ→cone-at ((j , j') , g) = pwᴱ.intro (w ⟅ j ⟆) (D ⟅ j' ⟆) (t ⟦ j ⟧ V.⋆ post (D ⟪ g ⟫))

      private
        evᴱ-intro : ∀ {j j'} (g : J [ j , j' ])
          → (weightedᴱ→cone-at ((j , j') , g) V.⊗ₕ V.id) V.⋆ evᴱ j j' ≡ t ⟦ j ⟧ V.⋆ post (D ⟪ g ⟫)
        evᴱ-intro {j} {j'} g = pwᴱ.β (w ⟅ j ⟆) (D ⟅ j' ⟆)

      weightedᴱ→cone : NatTrans (ΔCone ⟅ U ⟆) (Hom[_,-] ℰ W ∘F E)
      weightedᴱ→cone .N-ob = weightedᴱ→cone-at
      weightedᴱ→cone .N-hom {(j , j') , g} {(k , k') , h} ((u , v) , p) =
        V.⋆IdL _ ∙ pwᴱ.extensionality (w ⟅ k ⟆) (D ⟅ k' ⟆) (sym (
          ((weightedᴱ→cone-at ((j , j') , g) V.⋆ post (⋔ ⟪ w ⟪ u ⟫ , D ⟪ v ⟫ ⟫)) V.⊗ₕ V.id)
            V.⋆ evᴱ k k'
            ≡⟨ cong (V._⋆ evᴱ k k') (⊗id-seq _ _) ∙ V.⋆Assoc _ _ _
             ∙ cong ((weightedᴱ→cone-at ((j , j') , g) V.⊗ₕ V.id) V.⋆_) (powβᴱ (w ⟪ u ⟫) (D ⟪ v ⟫)) ⟩
          (weightedᴱ→cone-at ((j , j') , g) V.⊗ₕ V.id)
            V.⋆ ((V.id V.⊗ₕ w ⟪ u ⟫) V.⋆ (evᴱ j j' V.⋆ post (D ⟪ v ⟫)))
            ≡⟨ sym (V.⋆Assoc _ _ _)
             ∙ cong (V._⋆ (evᴱ j j' V.⋆ post (D ⟪ v ⟫))) (sym serialize₁₂ ∙ serialize₂₁)
             ∙ V.⋆Assoc _ _ _
             ∙ cong ((V.id V.⊗ₕ w ⟪ u ⟫) V.⋆_)
                 (sym (V.⋆Assoc _ _ _) ∙ cong (V._⋆ post (D ⟪ v ⟫)) (evᴱ-intro g)) ⟩
          (V.id V.⊗ₕ w ⟪ u ⟫) V.⋆ ((t ⟦ j ⟧ V.⋆ post (D ⟪ g ⟫)) V.⋆ post (D ⟪ v ⟫))
            ≡⟨ sym (V.⋆Assoc _ _ _) ∙ cong (V._⋆ post (D ⟪ v ⟫)) (sym (V.⋆Assoc _ _ _)) ⟩
          (((V.id V.⊗ₕ w ⟪ u ⟫) V.⋆ t ⟦ j ⟧) V.⋆ post (D ⟪ g ⟫)) V.⋆ post (D ⟪ v ⟫)
            ≡⟨ cong (λ m → (m V.⋆ post (D ⟪ g ⟫)) V.⋆ post (D ⟪ v ⟫)) (t .N-hom u) ⟩
          ((t ⟦ k ⟧ V.⋆ post (D ⟪ u ⟫)) V.⋆ post (D ⟪ g ⟫)) V.⋆ post (D ⟪ v ⟫)
            ≡⟨ V.⋆Assoc _ _ _ ∙ V.⋆Assoc _ _ _
             ∙ cong (t ⟦ k ⟧ V.⋆_)
                 (cong (post (D ⟪ u ⟫) V.⋆_) (sym (Hom[_,-] ℰ W .F-seq _ _))
                 ∙ sym (Hom[_,-] ℰ W .F-seq _ _)
                 ∙ cong post (cong (D ⟪ u ⟫ C.⋆_) (sym (D .F-seq g v)) ∙ sym (D .F-seq u (g J.⋆ v))
                              ∙ cong (D ⟪_⟫) (sym (J.⋆Assoc u g v) ∙ p))) ⟩
          t ⟦ k ⟧ V.⋆ post (D ⟪ h ⟫)
            ≡⟨ sym (evᴱ-intro h) ⟩
          (weightedᴱ→cone-at ((k , k') , h) V.⊗ₕ V.id) V.⋆ evᴱ k k' ∎))

    Conesᴱ≅WeightedConesᴱ : PshIso (Cones (Hom[_,-] ℰ W ∘F E)) (WeightedConesᴱ ℰ w D W)
    Conesᴱ≅WeightedConesᴱ .PshIso.trans .PshHom.N-ob U = coneᴱ→weighted
    Conesᴱ≅WeightedConesᴱ .PshIso.trans .PshHom.N-hom U' U f c = makeNatTransPath (funExt λ j →
      cong (V._⋆ evᴱ j j) (⊗id-seq _ _) ∙ V.⋆Assoc _ _ _)
    Conesᴱ≅WeightedConesᴱ .PshIso.nIso U .fst = weightedᴱ→cone
    Conesᴱ≅WeightedConesᴱ .PshIso.nIso U .snd .fst t = makeNatTransPath (funExt λ j →
      pwᴱ.β (w ⟅ j ⟆) (D ⟅ j ⟆)
      ∙ cong (t ⟦ j ⟧ V.⋆_) (cong post (D .F-id) ∙ Hom[_,-] ℰ W .F-id)
      ∙ V.⋆IdR _)
    Conesᴱ≅WeightedConesᴱ .PshIso.nIso U .snd .snd c = makeNatTransPath (funExt λ ((j , j') , g) →
      cong (pwᴱ.intro (w ⟅ j ⟆) (D ⟅ j' ⟆)) (at-postᴱ c g)
      ∙ sym (pwᴱ.η (w ⟅ j ⟆) (D ⟅ j' ⟆)))

  EnrichedLimit→EnrichedWeightedLimit : EnrichedLimit ℰ E → EnrichedWeightedLimit ℰ w D
  EnrichedLimit→EnrichedWeightedLimit lim .fst = limit→WeightedLimit (lim .fst)
  EnrichedLimit→EnrichedWeightedLimit lim .snd W =
    substIsUniversal (WeightedConesᴱ ℰ w D W)
      (seqIsUniversalPshIso (lim .snd W) (Conesᴱ≅WeightedConesᴱ W))
      (makeNatTransPath (funExt λ j →
        sym (preservesPowerCones ℰ (w ⟅ j ⟆) (D ⟅ j ⟆) W .PshHom.N-hom _ _
              (lim .fst .UniversalElement.element ⟦ idTw j ⟧) (ev j j))))
