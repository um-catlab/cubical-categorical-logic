{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Monoidal.Guarded

module Cubical.Categories.Enriched.Enrichment.LocallyContractive.Bifunctor
  {ℓ ℓ' : Level} {A : Category ℓ ℓ'} {ℓS : Level} (G : GuardedModel (PshMon.𝓟Mon A ℓS)) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Data.Unit
open import Cubical.Categories.NaturalTransformation using (NatTrans)
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Functor using (LaxMonoidalFunctor)
open import Cubical.Categories.Monoidal.NaturalTransformation.Base using (MonoidalNatTrans)
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed using (×PshIntroStrict)
open import Cubical.Categories.Enriched.Enrichment.Base
import Cubical.Categories.Enriched.Enrichment.Functor.Base as FE
open FE using (EnrichmentFor)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Product A ℓS

open Functor
open PshHomStrict
open PshMon A ℓS using (𝓟Mon ; 𝓟 ; 𝟙)
open GuardedModel G

private
  variable
    ℓC ℓC' ℓD₁ ℓD₁' ℓD₂ ℓD₂' ℓE ℓE' ℓB ℓB' : Level

  module ▷L = LaxMonoidalFunctor ▷Lax
  module nextNT = MonoidalNatTrans next

  pt : ∀ {P Q : Category.ob 𝓟} {α β : 𝓟 [ P , Q ]} → α ≡ β → ∀ c x → α .N-ob c x ≡ β .N-ob c x
  pt p c x i = p i .N-ob c x

  next-nat : {C : Category ℓC ℓC'} {D : Category ℓD₁ ℓD₁'}
    {ℰC : Enrichment C 𝓟Mon} {ℰD : Enrichment D 𝓟Mon} {F : Functor C D}
    (F̃ : FE.Enrichment 𝓟Mon ℰC ℰD F) {x y : Category.ob C} (f : C [ x , y ]) (c : Category.ob A) (t : ⟨ 𝟙 .F-ob c ⟩)
    → next⟦ _ ⟧ .N-ob c (Enrichment.⌜_⌝ ℰD (F ⟪ f ⟫) .N-ob c t)
      ≡ ▷L.F-hom (F̃ .FE.Enrichment.F[_,_] x y) .N-ob c
          (next⟦ _ ⟧ .N-ob c (Enrichment.⌜_⌝ ℰC f .N-ob c t))
  next-nat {ℰC = ℰC} {ℰD} F̃ {x} {y} f c t =
    cong (next⟦ _ ⟧ .N-ob c) (pt (F̃ .FE.Enrichment.agree f) c t)
    ∙ pt (nextNT.φ .NatTrans.N-hom (F̃ .FE.Enrichment.F[_,_] x y)) c (Enrichment.⌜_⌝ ℰC f .N-ob c t)

module _ {B : Category ℓB ℓB'} {C : Category ℓC ℓC'} {E : Category ℓE ℓE'}
  {ℰB : Enrichment B 𝓟Mon} {ℰC : Enrichment C 𝓟Mon} {ℰE : Enrichment E 𝓟Mon}
  {f : Category.ob B → Category.ob C} {g : Category.ob C → Category.ob E}
  (H : EnrichmentFor 𝓟Mon ℰC ℰE g) (F : EnrichmentFor 𝓟Mon ℰB ℰC f) where
  private
    module F = EnrichmentFor F
    module H = EnrichmentFor H

  _∘EnrFor_ : EnrichmentFor 𝓟Mon ℰB ℰE (λ x → g (f x))
  _∘EnrFor_ .EnrichmentFor.f[_,_] x y = F.f[ x , y ] ⋆PshHomStrict H.f[ f x , f y ]
  _∘EnrFor_ .EnrichmentFor.fid = makePshHomStrictPath (funExt λ c → funExt λ t →
    cong (H.f[ _ , _ ] .N-ob c) (pt F.fid c t) ∙ pt H.fid c t)
  _∘EnrFor_ .EnrichmentFor.f-seq = makePshHomStrictPath (funExt λ c → funExt λ (a , b) →
    pt H.f-seq c (F.f[ _ , _ ] .N-ob c a , F.f[ _ , _ ] .N-ob c b)
    ∙ cong (H.f[ _ , _ ] .N-ob c) (pt F.f-seq c (a , b)))

module _ {D₁ : Category ℓD₁ ℓD₁'} {D₂ : Category ℓD₂ ℓD₂'}
  {E : Category ℓE ℓE'}
  {ℰD₁ : Enrichment D₁ 𝓟Mon} {ℰD₂ : Enrichment D₂ 𝓟Mon}
  {ℰE : Enrichment E 𝓟Mon} where
  private
    module ℰD₁ = Enrichment ℰD₁
    module ℰD₂ = Enrichment ℰD₂
    module ℰE = Enrichment ℰE

  isLocallyContractiveˡʳ : Functor (D₁ ×C D₂) E → Type _
  isLocallyContractiveˡʳ Φ = Σ[ Φ̂ ∈ EnrichmentFor 𝓟Mon (Later.▷ℰ G ℰD₁ ×ᴱ Later.▷ℰ G ℰD₂) ℰE (Φ .F-ob) ]
    (∀ {x y : Category.ob (D₁ ×C D₂)} (f : (D₁ ×C D₂) [ x , y ]) →
      ℰE.⌜ Φ ⟪ f ⟫ ⌝ ≡ ×PshIntroStrict (ℰD₁.⌜ f .fst ⌝ ⋆PshHomStrict next⟦ ℰD₁.VE[ x .fst , y .fst ] ⟧)
                                      (ℰD₂.⌜ f .snd ⌝ ⋆PshHomStrict next⟦ ℰD₂.VE[ x .snd , y .snd ] ⟧)
                         ⋆PshHomStrict Φ̂ .EnrichmentFor.f[_,_] x y)

  isLocallyContractiveˡ : Functor (D₁ ×C D₂) E → Type _
  isLocallyContractiveˡ Φ = Σ[ Φ̂ ∈ EnrichmentFor 𝓟Mon (Later.▷ℰ G ℰD₁ ×ᴱ ℰD₂) ℰE (Φ .F-ob) ]
    (∀ {x y : Category.ob (D₁ ×C D₂)} (f : (D₁ ×C D₂) [ x , y ]) →
      ℰE.⌜ Φ ⟪ f ⟫ ⌝ ≡ ×PshIntroStrict (ℰD₁.⌜ f .fst ⌝ ⋆PshHomStrict next⟦ ℰD₁.VE[ x .fst , y .fst ] ⟧) ℰD₂.⌜ f .snd ⌝
                         ⋆PshHomStrict Φ̂ .EnrichmentFor.f[_,_] x y)

  isLocallyContractiveʳ : Functor (D₁ ×C D₂) E → Type _
  isLocallyContractiveʳ Φ = Σ[ Φ̂ ∈ EnrichmentFor 𝓟Mon (ℰD₁ ×ᴱ Later.▷ℰ G ℰD₂) ℰE (Φ .F-ob) ]
    (∀ {x y : Category.ob (D₁ ×C D₂)} (f : (D₁ ×C D₂) [ x , y ]) →
      ℰE.⌜ Φ ⟪ f ⟫ ⌝ ≡ ×PshIntroStrict ℰD₁.⌜ f .fst ⌝
                                      (ℰD₂.⌜ f .snd ⌝ ⋆PshHomStrict next⟦ ℰD₂.VE[ x .snd , y .snd ] ⟧)
                         ⋆PshHomStrict Φ̂ .EnrichmentFor.f[_,_] x y)

  module _ {C : Category ℓC ℓC'} {ℰC : Enrichment C 𝓟Mon}
    {Φ : Functor (D₁ ×C D₂) E} {F₁ : Functor C D₁} {F₂ : Functor C D₂} where
    LCˡʳ-precomp : isLocallyContractiveˡʳ Φ
      → FE.Enrichment 𝓟Mon ℰC ℰD₁ F₁ → FE.Enrichment 𝓟Mon ℰC ℰD₂ F₂
      → isLocallyContractive G ℰC ℰE (Φ ∘F (F₁ ,F F₂))
    LCˡʳ-precomp (Φ̂ , Φ-agree) F̃₁ F̃₂ .fst =
      Φ̂ ∘EnrFor (▷EnrFor G (forgetAgree G F̃₁) ,EnrFor ▷EnrFor G (forgetAgree G F̃₂))
    LCˡʳ-precomp (Φ̂ , Φ-agree) F̃₁ F̃₂ .snd {x} {y} f = makePshHomStrictPath (funExt λ c → funExt λ t →
      pt (Φ-agree {F₁ ⟅ x ⟆ , F₂ ⟅ x ⟆} {F₁ ⟅ y ⟆ , F₂ ⟅ y ⟆} (F₁ ⟪ f ⟫ , F₂ ⟪ f ⟫)) c t
      ∙ cong₂ (λ a b → Φ̂ .EnrichmentFor.f[_,_] (F₁ ⟅ x ⟆ , F₂ ⟅ x ⟆) (F₁ ⟅ y ⟆ , F₂ ⟅ y ⟆) .N-ob c (a , b))
          (next-nat F̃₁ f c t) (next-nat F̃₂ f c t))

    LCˡ-precomp : isLocallyContractiveˡ Φ
      → FE.Enrichment 𝓟Mon ℰC ℰD₁ F₁ → isLocallyContractive G ℰC ℰD₂ F₂
      → isLocallyContractive G ℰC ℰE (Φ ∘F (F₁ ,F F₂))
    LCˡ-precomp (Φ̂ , Φ-agree) F̃₁ (F̂₂ , F₂-agree) .fst =
      Φ̂ ∘EnrFor (▷EnrFor G (forgetAgree G F̃₁) ,EnrFor F̂₂)
    LCˡ-precomp (Φ̂ , Φ-agree) F̃₁ (F̂₂ , F₂-agree) .snd {x} {y} f =
      makePshHomStrictPath (funExt λ c → funExt λ t →
        pt (Φ-agree {F₁ ⟅ x ⟆ , F₂ ⟅ x ⟆} {F₁ ⟅ y ⟆ , F₂ ⟅ y ⟆} (F₁ ⟪ f ⟫ , F₂ ⟪ f ⟫)) c t
        ∙ cong₂ (λ a b → Φ̂ .EnrichmentFor.f[_,_] (F₁ ⟅ x ⟆ , F₂ ⟅ x ⟆) (F₁ ⟅ y ⟆ , F₂ ⟅ y ⟆) .N-ob c (a , b))
            (next-nat F̃₁ f c t) (pt (F₂-agree f) c t))

    LC-pair : FE.Enrichment 𝓟Mon (ℰD₁ ×ᴱ ℰD₂) ℰE Φ
      → isLocallyContractive G ℰC ℰD₁ F₁ → isLocallyContractive G ℰC ℰD₂ F₂
      → isLocallyContractive G ℰC ℰE (Φ ∘F (F₁ ,F F₂))
    LC-pair Φ̃ (F̂₁ , F₁-agree) (F̂₂ , F₂-agree) .fst =
      forgetAgree G Φ̃ ∘EnrFor (F̂₁ ,EnrFor F̂₂)
    LC-pair Φ̃ (F̂₁ , F₁-agree) (F̂₂ , F₂-agree) .snd {x} {y} f =
      makePshHomStrictPath (funExt λ c → funExt λ t →
        pt (Φ̃ .FE.Enrichment.agree {F₁ ⟅ x ⟆ , F₂ ⟅ x ⟆} {F₁ ⟅ y ⟆ , F₂ ⟅ y ⟆} (F₁ ⟪ f ⟫ , F₂ ⟪ f ⟫)) c t
        ∙ cong₂ (λ a b → Φ̃ .FE.Enrichment.F[_,_] (F₁ ⟅ x ⟆ , F₂ ⟅ x ⟆) (F₁ ⟅ y ⟆ , F₂ ⟅ y ⟆) .N-ob c (a , b))
            (pt (F₁-agree f) c t) (pt (F₂-agree f) c t))

    LCʳ-precomp : isLocallyContractiveʳ Φ
      → isLocallyContractive G ℰC ℰD₁ F₁ → FE.Enrichment 𝓟Mon ℰC ℰD₂ F₂
      → isLocallyContractive G ℰC ℰE (Φ ∘F (F₁ ,F F₂))
    LCʳ-precomp (Φ̂ , Φ-agree) (F̂₁ , F₁-agree) F̃₂ .fst =
      Φ̂ ∘EnrFor (F̂₁ ,EnrFor ▷EnrFor G (forgetAgree G F̃₂))
    LCʳ-precomp (Φ̂ , Φ-agree) (F̂₁ , F₁-agree) F̃₂ .snd {x} {y} f =
      makePshHomStrictPath (funExt λ c → funExt λ t →
        pt (Φ-agree {F₁ ⟅ x ⟆ , F₂ ⟅ x ⟆} {F₁ ⟅ y ⟆ , F₂ ⟅ y ⟆} (F₁ ⟪ f ⟫ , F₂ ⟪ f ⟫)) c t
        ∙ cong₂ (λ a b → Φ̂ .EnrichmentFor.f[_,_] (F₁ ⟅ x ⟆ , F₂ ⟅ x ⟆) (F₁ ⟅ y ⟆ , F₂ ⟅ y ⟆) .N-ob c (a , b))
            (pt (F₁-agree f) c t) (next-nat F̃₂ f c t))

module _ {C : Category ℓC ℓC'} {D : Category ℓD₁ ℓD₁'}
  (ℰC : Enrichment C 𝓟Mon) (ℰD : Enrichment D 𝓟Mon) (K : Category.ob D) where
  private
    module ℰD = Enrichment ℰD

  LC-const : isLocallyContractive G ℰC ℰD (Constant C D K)
  LC-const .fst .EnrichmentFor.f[_,_] x y .N-ob c _ = ℰD.id .N-ob c tt*
  LC-const .fst .EnrichmentFor.f[_,_] x y .N-hom c c' k _ _ _ = ℰD.id .N-hom c c' k tt* tt* refl
  LC-const .fst .EnrichmentFor.fid = makePshHomStrictPath refl
  LC-const .fst .EnrichmentFor.f-seq = makePshHomStrictPath (funExt λ c → funExt λ _ →
    sym (pt (ℰD.⋆IdL K K) c (tt* , ℰD.id .N-ob c tt*)))
  LC-const .snd f = makePshHomStrictPath (funExt λ c → funExt λ t → pt ℰD.⌜id⌝ c t)
