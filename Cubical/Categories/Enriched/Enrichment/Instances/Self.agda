{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Enrichment.Instances.Self where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Closed
open import Cubical.Categories.Monoidal.Dual

open import Cubical.Foundations.Isomorphism
open import Cubical.Categories.Category
open import Cubical.Categories.NaturalTransformation using (NatTrans ; NatIso)
open import Cubical.Categories.Reasoning.Core
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.Functor.Base using (EnrichmentFor)
open import Cubical.Categories.Enriched.Enrichment.Instances.Underlying
open import Cubical.Categories.Monoidal.Functor
import Cubical.Categories.Enriched.BaseChange.Base as EnrBC
open import Cubical.Categories.Monoidal.Properties using (ρ⟨⊗⟩)

module _ {ℓ ℓ' : Level} (V : MonoidalCategory ℓ ℓ') (cl : LeftClosed V) where
  open MonoidalCategory V
  open Reasoning C
  open import Cubical.Categories.Monoidal.Reasoning V
  open LeftClosedNotation cl

  ev-pre : ∀ {c d w z} (k : Hom[ w , z ]) (h : Hom[ c ⊗ z , d ])
    → (id ⊗ₕ (k ⋆ lda h)) ⋆ ev ≡ (id ⊗ₕ k) ⋆ h
  ev-pre k h = cong (_⋆ ev) split₂ʳ ∙ ⋆Assoc _ _ _ ∙ cong ((id ⊗ₕ k) ⋆_) (ev-β h)

  private
    α-nat : ∀ {x x' y y' z z'} (f : Hom[ x , x' ]) (g : Hom[ y , y' ]) (h : Hom[ z , z' ])
      → (f ⊗ₕ (g ⊗ₕ h)) ⋆ α⟨ x' , y' , z' ⟩ ≡ α⟨ x , y , z ⟩ ⋆ ((f ⊗ₕ g) ⊗ₕ h)
    α-nat f g h = α .NatIso.trans .NatTrans.N-hom (f , g , h)

    ρ-nat : ∀ {x y} (f : Hom[ x , y ]) → (f ⊗ₕ id) ⋆ ρ⟨ y ⟩ ≡ ρ⟨ x ⟩ ⋆ f
    ρ-nat f = ρ .NatIso.trans .NatTrans.N-hom f

    interchange : ∀ {a b c d d'} (f : Hom[ a ⊗ b , c ]) (g : Hom[ d , d' ])
      → ((id {a} ⊗ₕ id {b}) ⊗ₕ g) ⋆ (f ⊗ₕ id) ≡ (f ⊗ₕ id) ⋆ (id ⊗ₕ g)
    interchange f g =
      sym ⊗-distrib-over-⋆
      ∙ ⟨ cong (_⋆ f) ⊗-id ∙ ⋆IdL f ∙ sym (⋆IdR f) ⟩⊗⟨ ⋆IdR g ∙ sym (⋆IdL g) ⟩
      ∙ ⊗-distrib-over-⋆

    idE : ∀ {x} → Hom[ unit , x ⟜ x ]
    idE {x} = lda ρ⟨ x ⟩

    seqBody : ∀ x y z → Hom[ x ⊗ ((y ⟜ x) ⊗ (z ⟜ y)) , z ]
    seqBody x y z = α⟨ x , y ⟜ x , z ⟜ y ⟩ ⋆ ((ev ⊗ₕ id) ⋆ ev)

    seqE : ∀ x y z → Hom[ (y ⟜ x) ⊗ (z ⟜ y) , z ⟜ x ]
    seqE x y z = lda (seqBody x y z)

    ⌜_⌝ : ∀ {x y} → Hom[ x , y ] → Hom[ unit , y ⟜ x ]
    ⌜ f ⌝ = lda (ρ⟨ _ ⟩ ⋆ f)

    ⇄ : ∀ {x y} → Iso Hom[ x , y ] Hom[ unit , y ⟜ x ]
    ⇄ .Iso.fun = ⌜_⌝
    ⇄ .Iso.inv g = ρ⁻¹⟨ _ ⟩ ⋆ ((id ⊗ₕ g) ⋆ ev)
    ⇄ .Iso.sec g = ⟜-ext (ev-β _ ∙ pullˡ (ρ .NatIso.nIso _ .isIso.ret) ∙ ⋆IdL _)
    ⇄ .Iso.ret f =
      cong (ρ⁻¹⟨ _ ⟩ ⋆_) (ev-β _) ∙ pullˡ (ρ .NatIso.nIso _ .isIso.sec) ∙ ⋆IdL f

    seqE-IdL : ∀ x y → η⟨ y ⟜ x ⟩ ≡ (idE ⊗ₕ id) ⋆ seqE x x y
    seqE-IdL x y = ⟜-ext (sym (
        ev-pre _ _
      ∙ extendʳ (α-nat id idE id)
      ∙ cong (α⟨ _ , _ , _ ⟩ ⋆_) (pullˡ merge₁ˡ)
      ∙ cong (λ m → α⟨ _ , _ , _ ⟩ ⋆ ((m ⊗ₕ id) ⋆ ev)) (ev-β ρ⟨ x ⟩)
      ∙ pullˡ (triangle _ _)))

    seqE-IdR : ∀ x y → ρ⟨ y ⟜ x ⟩ ≡ (id ⊗ₕ idE) ⋆ seqE x y y
    seqE-IdR x y = ⟜-ext (sym (
        ev-pre _ _
      ∙ extendʳ (α-nat id id idE)
      ∙ cong (α⟨ _ , _ , _ ⟩ ⋆_) (extendʳ (interchange ev idE))
      ∙ cong (λ m → α⟨ _ , _ , _ ⟩ ⋆ ((ev ⊗ₕ id) ⋆ m)) (ev-β ρ⟨ y ⟩)
      ∙ cong (α⟨ _ , _ , _ ⟩ ⋆_) (ρ-nat ev)
      ∙ pullˡ (ρ⟨⊗⟩ V)))

    seqE-Assoc : ∀ x y z w →
      α⟨ _ , _ , _ ⟩ ⋆ ((seqE x y z ⊗ₕ id) ⋆ seqE x z w)
      ≡ (id ⊗ₕ seqE y z w) ⋆ seqE x y w
    seqE-Assoc x y z w = ⟜-ext (lhs ∙ sym rhs)
      where
      E₁ = ev {x} {y}
      E₂ = ev {y} {z}
      E₃ = ev {z} {w}
      common : Hom[ x ⊗ ((y ⟜ x) ⊗ ((z ⟜ y) ⊗ (w ⟜ z))) , w ]
      common = α⟨ _ , _ , _ ⟩ ⋆ (α⟨ _ , _ , _ ⟩ ⋆ (((E₁ ⊗ₕ id) ⊗ₕ id) ⋆ ((E₂ ⊗ₕ id) ⋆ E₃)))

      lhs : (id ⊗ₕ (α⟨ _ , _ , _ ⟩ ⋆ ((seqE x y z ⊗ₕ id) ⋆ seqE x z w))) ⋆ ev ≡ common
      lhs =
          cong (λ m → (id ⊗ₕ m) ⋆ ev) (sym (⋆Assoc _ _ _))
        ∙ ev-pre _ (seqBody x z w)
        ∙ cong (_⋆ seqBody x z w) split₂ʳ
        ∙ ⋆Assoc _ _ _
        ∙ cong ((id ⊗ₕ α⟨ _ , _ , _ ⟩) ⋆_)
            ( extendʳ (α-nat id (seqE x y z) id)
            ∙ cong (α⟨ _ , _ , _ ⟩ ⋆_)
                ( pullˡ merge₁ˡ
                ∙ cong (λ m → (m ⊗ₕ id) ⋆ E₃) (ev-β (seqBody x y z))
                ∙ cong (_⋆ E₃) (split₁ˡ ∙ cong ((α⟨ _ , _ , _ ⟩ ⊗ₕ id) ⋆_) split₁ˡ)
                ∙ ⋆Assoc _ _ _ ∙ cong ((α⟨ _ , _ , _ ⟩ ⊗ₕ id) ⋆_) (⋆Assoc _ _ _)))
        ∙ cong ((id ⊗ₕ α⟨ _ , _ , _ ⟩) ⋆_) (sym (⋆Assoc _ _ _))
        ∙ sym (⋆Assoc _ _ _)
        ∙ cong (_⋆ (((E₁ ⊗ₕ id) ⊗ₕ id) ⋆ ((E₂ ⊗ₕ id) ⋆ E₃)))
            (pentagon x (y ⟜ x) (z ⟜ y) (w ⟜ z))
        ∙ ⋆Assoc _ _ _

      rhs : (id ⊗ₕ ((id ⊗ₕ seqE y z w) ⋆ seqE x y w)) ⋆ ev ≡ common
      rhs =
          ev-pre _ (seqBody x y w)
        ∙ extendʳ (α-nat id id (seqE y z w))
        ∙ cong (α⟨ _ , _ , _ ⟩ ⋆_)
            ( extendʳ (interchange E₁ (seqE y z w))
            ∙ cong ((E₁ ⊗ₕ id) ⋆_) (ev-β (seqBody y z w))
            ∙ cong (_⋆ seqBody y z w) (cong (E₁ ⊗ₕ_) (sym (⊗-id {z ⟜ y} {w ⟜ z})))
            ∙ extendʳ (α-nat E₁ (id {z ⟜ y}) (id {w ⟜ z})))

    ⌜⋆⌝E : ∀ {x y z} (f : Hom[ x , y ]) (g : Hom[ y , z ])
      → ⌜ f ⋆ g ⌝ ≡ η⁻¹⟨ _ ⟩ ⋆ ((⌜ f ⌝ ⊗ₕ ⌜ g ⌝) ⋆ seqE x y z)
    ⌜⋆⌝E {x} {y} {z} f g = ⟜-ext (ev-β (ρ⟨ x ⟩ ⋆ (f ⋆ g)) ∙ sym (
        cong (λ m → (id ⊗ₕ m) ⋆ ev) (sym (⋆Assoc _ _ _))
      ∙ ev-pre _ (seqBody x y z)
      ∙ cong (_⋆ seqBody x y z) split₂ʳ
      ∙ ⋆Assoc _ _ _
      ∙ cong ((id ⊗ₕ η⁻¹⟨ _ ⟩) ⋆_)
          ( extendʳ (α-nat id ⌜ f ⌝ ⌜ g ⌝)
          ∙ cong (α⟨ _ , _ , _ ⟩ ⋆_)
              ( pullˡ (sym split₁ʳ)
              ∙ cong (λ m → (m ⊗ₕ ⌜ g ⌝) ⋆ ev) (ev-β (ρ⟨ x ⟩ ⋆ f))
              ∙ cong (_⋆ ev) split₁ˡ
              ∙ ⋆Assoc _ _ _)
          ∙ pullˡ (triangle _ _))
      ∙ pullˡ (merge₂ʳ ∙ cong (id ⊗ₕ_) (η .NatIso.nIso _ .isIso.sec) ∙ ⊗-id)
      ∙ ⋆IdL _
      ∙ cong (_⋆ ev) serialize₁₂
      ∙ ⋆Assoc _ _ _
      ∙ cong ((f ⊗ₕ id) ⋆_) (ev-β (ρ⟨ y ⟩ ⋆ g))
      ∙ pullˡ (ρ-nat f)
      ∙ ⋆Assoc _ _ _))

  leftSelfEnrichment : Enrichment C V
  leftSelfEnrichment .Enrichment.VE[_,_] x y = y ⟜ x
  leftSelfEnrichment .Enrichment.id = idE
  leftSelfEnrichment .Enrichment.seq = seqE
  leftSelfEnrichment .Enrichment.⇄-agree = ⇄
  leftSelfEnrichment .Enrichment.⋆IdL = seqE-IdL
  leftSelfEnrichment .Enrichment.⋆IdR = seqE-IdR
  leftSelfEnrichment .Enrichment.⋆Assoc = seqE-Assoc
  leftSelfEnrichment .Enrichment.⌜id⌝ = cong lda (⋆IdR _)
  leftSelfEnrichment .Enrichment.⌜⋆⌝ = ⌜⋆⌝E

  module _ (F : LaxMonoidalFunctor V V) where
    private
      module F = LaxMonoidalFunctor F

    F-pre : ∀ {a b b'} (g : Hom[ b , b' ])
      → (id {F.F-ob a} ⊗ₕ F.F-hom g) ⋆ F.μ⟨ a , b' ⟩ ≡ F.μ⟨ a , b ⟩ ⋆ F.F-hom (id ⊗ₕ g)
    F-pre g =
      cong (λ m → (m ⊗ₕ F.F-hom g) ⋆ F.μ⟨ _ , _ ⟩) (sym F.F-id)
      ∙ F.μ .NatTrans.N-hom (id , g)

    F-post : ∀ {a a' b} (g : Hom[ a , a' ])
      → (F.F-hom g ⊗ₕ id {F.F-ob b}) ⋆ F.μ⟨ a' , b ⟩ ≡ F.μ⟨ a , b ⟩ ⋆ F.F-hom (g ⊗ₕ id)
    F-post g =
      cong (λ m → (F.F-hom g ⊗ₕ m) ⋆ F.μ⟨ _ , _ ⟩) (sym F.F-id)
      ∙ F.μ .NatTrans.N-hom (g , id)

    ε-pre : ∀ {a b c} (g : Hom[ unit , b ]) (h : Hom[ a ⊗ b , c ]) (k : Hom[ a , c ])
      → (id ⊗ₕ g) ⋆ h ≡ ρ⟨ a ⟩ ⋆ k
      → (id ⊗ₕ (F.ε ⋆ F.F-hom g)) ⋆ (F.μ⟨ a , b ⟩ ⋆ F.F-hom h) ≡ ρ⟨ F.F-ob a ⟩ ⋆ F.F-hom k
    ε-pre g h k p =
        cong (_⋆ (F.μ⟨ _ , _ ⟩ ⋆ F.F-hom h)) split₂ʳ
      ∙ ⋆Assoc _ _ _
      ∙ cong ((id ⊗ₕ F.ε) ⋆_) (extendʳ (F-pre g))
      ∙ cong (λ m → (id ⊗ₕ F.ε) ⋆ (F.μ⟨ _ , _ ⟩ ⋆ m))
          (sym (F.F-seq _ _) ∙ cong F.F-hom p ∙ F.F-seq _ _)
      ∙ cong ((id ⊗ₕ F.ε) ⋆_) (sym (⋆Assoc _ _ _))
      ∙ sym (⋆Assoc _ _ _)
      ∙ cong (_⋆ F.F-hom k) (sym (⋆Assoc _ _ _) ∙ F.ρε-law _)

    private
      H : ∀ x y → Hom[ F.F-ob x ⊗ F.F-ob (y ⟜ x) , F.F-ob y ]
      H x y = F.μ⟨ x , y ⟜ x ⟩ ⋆ F.F-hom ev

      E = toEnrichedCategory C V leftSelfEnrichment

    laxEnrichment : EnrichmentFor V (Underlying (EnrBC.BaseChange F E)) leftSelfEnrichment F.F-ob
    laxEnrichment .EnrichmentFor.f[_,_] x y = lda (H x y)
    laxEnrichment .EnrichmentFor.fid {x} = ⟜-ext (
        ev-pre _ (H x x)
      ∙ ε-pre idE ev id (ev-β ρ⟨ x ⟩ ∙ sym (⋆IdR _))
      ∙ cong (ρ⟨ _ ⟩ ⋆_) F.F-id
      ∙ ⋆IdR _
      ∙ sym (ev-β ρ⟨ F.F-ob x ⟩))
    laxEnrichment .EnrichmentFor.f-seq {X} {Y} {Z} = ⟜-ext (lhs ∙ sym rhs)
      where
      fXY = lda (H X Y)
      fYZ = lda (H Y Z)
      common = (id ⊗ₕ F.μ⟨ _ , _ ⟩) ⋆ (F.μ⟨ _ , _ ⟩
        ⋆ (F.F-hom α⟨ X , Y ⟜ X , Z ⟜ Y ⟩ ⋆ (F.F-hom (ev ⊗ₕ id) ⋆ F.F-hom ev)))

      lhs : (id ⊗ₕ ((fXY ⊗ₕ fYZ) ⋆ seqE _ _ _)) ⋆ ev ≡ common
      lhs =
          ev-pre _ (seqBody (F.F-ob X) (F.F-ob Y) (F.F-ob Z))
        ∙ extendʳ (α-nat id fXY fYZ)
        ∙ cong (α⟨ _ , _ , _ ⟩ ⋆_)
            ( pullˡ (sym split₁ʳ)
            ∙ cong (λ m → (m ⊗ₕ fYZ) ⋆ ev) (ev-β (H X Y))
            ∙ cong (_⋆ ev) (serialize₁₂ ∙ cong (_⋆ (id ⊗ₕ fYZ)) split₁ˡ)
            ∙ ⋆Assoc _ _ _ ∙ ⋆Assoc _ _ _
            ∙ cong (λ m → (F.μ⟨ _ , _ ⟩ ⊗ₕ id) ⋆ ((F.F-hom ev ⊗ₕ id) ⋆ m)) (ev-β (H Y Z))
            ∙ cong ((F.μ⟨ _ , _ ⟩ ⊗ₕ id) ⋆_) (extendʳ (F-post ev))
            ∙ sym (⋆Assoc _ _ _))
        ∙ sym (⋆Assoc _ _ _)
        ∙ cong (_⋆ (F.F-hom (ev ⊗ₕ id) ⋆ F.F-hom ev))
            (sym (⋆Assoc _ _ _) ∙ F.αμ-law X (Y ⟜ X) (Z ⟜ Y))
        ∙ ⋆Assoc _ _ _ ∙ ⋆Assoc _ _ _

      rhs : (id ⊗ₕ ((F.μ⟨ _ , _ ⟩ ⋆ F.F-hom (seqE X Y Z)) ⋆ lda (H X Z))) ⋆ ev ≡ common
      rhs =
          ev-pre _ (H X Z)
        ∙ cong (_⋆ H X Z) split₂ʳ
        ∙ ⋆Assoc _ _ _
        ∙ cong ((id ⊗ₕ F.μ⟨ _ , _ ⟩) ⋆_) (extendʳ (F-pre (seqE X Y Z)))
        ∙ cong (λ m → (id ⊗ₕ F.μ⟨ _ , _ ⟩) ⋆ (F.μ⟨ _ , _ ⟩ ⋆ m))
            ( sym (F.F-seq _ _)
            ∙ cong F.F-hom (ev-β (seqBody X Y Z))
            ∙ F.F-seq _ _
            ∙ cong (F.F-hom α⟨ _ , _ , _ ⟩ ⋆_) (F.F-seq _ _))

module _ {ℓ ℓ' : Level} (V : MonoidalCategory ℓ ℓ') where
  rightSelfEnrichment : RightClosed V → Enrichment (MonoidalCategory.C V) (V ^co)
  rightSelfEnrichment cl = leftSelfEnrichment (V ^co) (RightClosed→LeftClosed^co V cl)
