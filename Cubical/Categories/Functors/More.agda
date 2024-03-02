{-# OPTIONS --safe #-}

module Cubical.Categories.Functors.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation as Prop

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    E : Category ℓE ℓE'

open Category
open Functor

ConstantComposeFunctor :
  (C : Category ℓC ℓC') (D : Category ℓD ℓD' ) (c : C .ob)
  (F : Functor C D) →
  Constant (D ^op) D (F .F-ob c) ≡ F ∘F Constant (D ^op) C c
ConstantComposeFunctor C D c F = Functor≡
  (λ c → ( refl ))
    (λ f → (
      D .id
     ≡⟨ sym (F .F-id) ⟩
       F ⟪ Constant (D ^op) C c ⟪ f ⟫ ⟫ ∎
  ))

-- The data of a functor, parameterized by the action on objects
record ActionOnMorphisms
  (C : Category ℓC ℓC')
  (D : Category ℓD ℓD')
  (F₀ : C .ob → D .ob) : Type (ℓ-max (ℓ-max ℓC ℓC') ℓD') where
  no-eta-equality

  open Category

  field
    F-hom : {x y : C .ob} → C [ x , y ] → D [ F₀ x , F₀ y ]
    F-id  : {x : C .ob} → F-hom (C .id) ≡ D .id {x = F₀ x}
    F-seq : {x y z : C .ob} (f : C [ x , y ]) (g : C [ y , z ])
          → F-hom (f ⋆⟨ C ⟩ g) ≡ (F-hom f) ⋆⟨ D ⟩ (F-hom g)

open ActionOnMorphisms

ActionOnMorphisms→Functor :
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}{F₀ : C .ob → D .ob}
                          → ActionOnMorphisms C D F₀
                          → Functor C D
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-ob = F₀
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-hom = F₁ .F-hom
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-id = F₁ .F-id
ActionOnMorphisms→Functor {F₀ = F₀} F₁ .F-seq = F₁ .F-seq

module _ {ℓC ℓC' ℓD ℓD' ℓE ℓE'}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  {G : Functor D E}
  (isFullyFaithfulG : isFullyFaithful G)
  where

  private
    GFF : ∀ {x y} → D [ x , y ] ≃ E [ G ⟅ x ⟆ , G ⟅ y ⟆ ]
    GFF = _ , (isFullyFaithfulG _ _)

    GFaith : ∀ {x y} → (D [ x , y ]) ↪ (E [ G ⟅ x ⟆ , G ⟅ y ⟆ ])
    GFaith = _ , isEquiv→isEmbedding (GFF .snd)
    -- this would be convenient as FF.Reasoning
    G-hom⁻ : ∀ {x y} → E [ G ⟅ x ⟆ , G ⟅ y ⟆ ] → D [ x , y ]
    G-hom⁻ = invIsEq (isFullyFaithfulG _ _)


  isFullyFaithfulPostcomposeF : isFullyFaithful (postcomposeF C G)
  isFullyFaithfulPostcomposeF F F' .equiv-proof α =
    uniqueExists
      (natTrans (λ x → G-hom⁻ (α ⟦ x ⟧)) λ f →
        isEmbedding→Inj (GFaith .snd) _ _
        ( G .F-seq _ _
        ∙ cong₂ (seq' E) refl (secEq GFF _)
        ∙ α.N-hom _
        ∙ sym (cong₂ (seq' E) (secEq GFF _) refl)
        ∙ sym (G .F-seq _ _)))
      (makeNatTransPath (funExt λ c → secIsEq (isFullyFaithfulG _ _) (α ⟦ c ⟧)))
      (λ _ → isSetNatTrans _ _)
      λ β G∘β≡α → makeNatTransPath (funExt λ c →
        isEmbedding→Inj (isEquiv→isEmbedding (isFullyFaithfulG _ _)) _ _
        (secIsEq (isFullyFaithfulG _ _) _ ∙ sym (cong (_⟦ c ⟧) G∘β≡α)))

    where module α = NatTrans α

module _ {F : Functor C D} {G : Functor D E} where
  open Category
  open Functor

  module _
    (isFullyFaithfulF : isFullyFaithful F)
    (isFullyFaithfulG : isFullyFaithful G)
    where
    isFullyFaithfulG∘F : isFullyFaithful (G ∘F F)
    isFullyFaithfulG∘F x y =
      equivIsEquiv
        (compEquiv (_ , isFullyFaithfulF x y)
                 (_ , isFullyFaithfulG (F ⟅ x ⟆) (F ⟅ y ⟆)))

  module _
    (isFullG : isFull G)
    (isFullF : isFull F)
    where
    isFullG∘F : isFull (G ∘F F)
    isFullG∘F x y G∘F[f] =
      rec
        isPropPropTrunc
        (λ Ff → rec
          isPropPropTrunc
          (λ f → ∣ f .fst , cong (G .F-hom) (f .snd) ∙ Ff .snd ∣₁)
          (isFullF x y (Ff .fst)))
        (isFullG (F ⟅ x ⟆) (F ⟅ y ⟆) G∘F[f])

  module _
    (isFaithfulF : isFaithful F)
    (isFaithfulG : isFaithful G)
    where

    isFaithfulG∘F : isFaithful (G ∘F F)
    isFaithfulG∘F x y =
      isEmbedding→Inj
        (compEmbedding
        ((λ v → F-hom G v) ,
          (injEmbedding (E .isSetHom) (isFaithfulG (F ⟅ x ⟆) (F ⟅ y ⟆) _ _)))
        ((λ z → F-hom F z) ,
          (injEmbedding (D .isSetHom) (isFaithfulF x y _ _))) .snd)
