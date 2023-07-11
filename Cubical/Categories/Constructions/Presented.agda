-- Free category quotiented by equations
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Presented where

open import Cubical.Categories.Morphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation hiding (rec)
open import Cubical.HITs.SetQuotients as Quotient
  renaming ([_] to [_]q) hiding (rec)

open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
  hiding (rec; ind)
private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓj : Level

open Category
open Functor
open NatIso hiding (sqRL; sqLL)
open NatTrans
open Quiver
open Interp

module _ (Q : Quiver ℓg ℓg') where
  FQ = FreeCat Q

  record Axioms ℓj : Type (ℓ-max (ℓ-max ℓg ℓg') (ℓ-suc ℓj)) where
    field
      equation : Type ℓj
      dom cod : equation → FQ .ob
      lhs rhs : ∀ eq → FQ [ dom eq , cod eq ]

  open Axioms
  mkAx : (Equation : Type ℓj) →
         (Equation →
           Σ[ A ∈ FQ .ob ] Σ[ B ∈ FQ .ob ] FQ [ A , B ] × FQ [ A , B ]) →
         Axioms ℓj
  mkAx Eq funs .equation = Eq
  mkAx Eq funs .dom eq = funs eq .fst
  mkAx Eq funs .cod eq = funs eq .snd .fst
  mkAx Eq funs .lhs eq = funs eq .snd .snd .fst
  mkAx Eq funs .rhs eq = funs eq .snd .snd .snd

  module _ (Ax : Axioms ℓj) where
    data _≈_ : ∀ {A B} → FQ [ A , B ] → FQ [ A , B ] →
               Type (ℓ-max (ℓ-max ℓg ℓg') ℓj) where
      ↑_ : ∀ eq → Ax .lhs eq ≈ Ax .rhs eq
      _⋆ₑr_ : ∀ {A B C} → (e₁ : FQ [ A , B ]) → {e₂ e₂' : FQ [ B , C ]}
            → e₂ ≈ e₂'
            → (e₁ ⋆ₑ e₂) ≈ (e₁ ⋆ₑ e₂')
      _⋆ₑl_ : ∀ {A B C} → {e₁ e₁' : FQ [ A , B ]}
            → (e₁ ≈ e₁') → (e₂ : FQ [ B , C ])
            → (e₁ ⋆ₑ e₂) ≈ (e₁' ⋆ₑ e₂)
      ⋆ₑIdL : ∀ {A B} (e : FQ [ A , B ]) → (idₑ ⋆ₑ e) ≈ e
      ⋆ₑIdR : ∀ {A B} (e : FQ [ A , B ]) → (e ⋆ₑ idₑ) ≈ e
      ⋆ₑAssoc : ∀ {A B C D} (e : FQ [ A , B ])
               (f : FQ [ B , C ])(g : FQ [ C , D ])
              → ((e ⋆ₑ f) ⋆ₑ g) ≈ (e ⋆ₑ (f ⋆ₑ g))

    compQ : ∀ {A B C}
          → ([f] : (FQ [ A , B ]) / _≈_) ([g] : (FQ [ B , C ]) / _≈_)
          → (FQ [ A , C ]) / _≈_
    compQ =
      Quotient.rec2 squash/
        (λ f g → [ f ⋆ₑ g ]q)
        (λ _ _ e p → eq/ _ _ (p ⋆ₑl _))
        (λ _ _ e p → eq/ _ _ (_ ⋆ₑr p))

    PresentedCat : Category _ _
    PresentedCat .ob = FQ .ob
    PresentedCat .Hom[_,_] A B = (FQ [ A , B ]) / _≈_
    PresentedCat .id = [ idₑ ]q
    PresentedCat ._⋆_ = compQ
    PresentedCat .⋆IdL = elimProp {P = λ [f] → compQ [ idₑ ]q [f] ≡ [f]}
      (λ _ → squash/ _ _)
      λ a → eq/ _ _ (⋆ₑIdL a)
    PresentedCat .⋆IdR = elimProp {P = λ [f] → compQ [f] [ idₑ ]q ≡ [f]}
      (λ _ → squash/ _ _)
      λ a → eq/ _ _ (⋆ₑIdR a)
    PresentedCat .⋆Assoc = elimProp3 (λ _ _ _ → squash/ _ _) (λ e f g →
      eq/ _ _ (⋆ₑAssoc e f g))
    PresentedCat .isSetHom = squash/

    FreeToPresented : Functor FQ PresentedCat
    FreeToPresented .F-ob x = x
    FreeToPresented .F-hom = [_]q
    FreeToPresented .F-id = refl
    FreeToPresented .F-seq f g = refl

    isFullFreeToPresented : isFull FreeToPresented
    isFullFreeToPresented A B = []surjective

    ηP : Interp Q PresentedCat
    ηP .I-ob = λ A → A
    ηP .I-hom = λ e → [ ↑ e ]q

    ηEq : ∀ eq → Path (PresentedCat [ Ax .dom eq , Ax .cod eq ])
                      [ Ax .lhs eq ]q
                      [ Ax .rhs eq ]q
    ηEq eq = eq/ _ _ (↑ eq)

    module _ (𝓒 : Category ℓc ℓc') (ı : Interp Q 𝓒) where
      Frec = Free.rec Q 𝓒 ı

      module _ (satisfies-axioms : ∀ eq →
        Frec ⟪ Ax .lhs eq ⟫ ≡ Frec ⟪ Ax .rhs eq ⟫) where
        rec-respects-≈ : ∀ {A B} {e e' : FQ [ A , B ]}
                       → e ≈ e'
                       → Frec ⟪ e ⟫ ≡ Frec ⟪ e' ⟫
        rec-respects-≈ (↑ eq) = satisfies-axioms eq
        rec-respects-≈ (e₁ ⋆ₑr p) = λ i → Frec ⟪ e₁ ⟫ ⋆⟨ 𝓒 ⟩ rec-respects-≈ p i
        rec-respects-≈ (p ⋆ₑl e₂) = λ i → rec-respects-≈ p i ⋆⟨ 𝓒 ⟩ Frec ⟪ e₂ ⟫
        rec-respects-≈ (⋆ₑIdL _) = 𝓒 .⋆IdL _
        rec-respects-≈ (⋆ₑIdR _) = 𝓒 .⋆IdR _
        rec-respects-≈ (⋆ₑAssoc e f g) = 𝓒 .⋆Assoc _ _ _

        rec : Functor PresentedCat 𝓒
        rec .F-ob = ı .I-ob
        rec .F-hom =
          Quotient.rec (𝓒 .isSetHom) (Frec .F-hom) (λ _ _ → rec-respects-≈)
        rec .F-id = refl
        rec .F-seq = elimProp2 (λ _ _ → 𝓒 .isSetHom _ _) (λ _ _ → refl)

recNT : {Q : Quiver ℓg ℓg'}{Ax : Axioms Q ℓj} {𝓒 : Category ℓc ℓc'}
        {F G : Functor (PresentedCat Q Ax) 𝓒}
        (α : ∀ (a : Q .ob) → 𝓒 [ F ⟅ a ⟆ , G ⟅ a ⟆ ])
        (p : ∀ (gen : Q .mor) →
          F ⟪ ηP Q Ax .I-hom gen ⟫ ⋆⟨ 𝓒 ⟩ α (Q .cod gen)
          ≡ α (Q .dom gen) ⋆⟨ 𝓒 ⟩ G ⟪ ηP Q Ax .I-hom gen ⟫)
      → NatTrans F G
recNT α p .N-ob = α
recNT {Q = Q}{𝓒 = 𝓒}{F = F}{G = G} α p .N-hom =
  elimProp (λ _ → 𝓒 .isSetHom _ _) isNat where
  isNatTy : ∀ {a b}(e : FQ Q [ a , b ]) → Type _
  isNatTy e = F ⟪ [ e ]q ⟫ ⋆⟨ 𝓒 ⟩ α _ ≡ α _ ⋆⟨ 𝓒 ⟩ G ⟪ [ e ]q ⟫

  isNat : ∀ {a b} e → isNatTy {a}{b} e
  isNat = elimExpProp Q {P = isNatTy}
    (λ e → 𝓒 .isSetHom _ _)
    p
    (λ {a} → cong₂ (seq' 𝓒)(F .F-id) refl
      ∙ 𝓒 .⋆IdL _ ∙ sym (𝓒 .⋆IdR _)
      ∙ cong₂ (seq' 𝓒) refl (sym (G .F-id)))
    λ e e' nat-e nat-e' →
      cong₂ (seq' 𝓒) (F .F-seq [ e ]q [ e' ]q) refl
      ∙ (𝓒 .⋆Assoc _ _ _
      ∙ cong₂ (seq' 𝓒) refl nat-e'
      ∙ sym (𝓒 .⋆Assoc _ _ _)
      ∙ cong₂ (seq' 𝓒) nat-e refl
      ∙ 𝓒 .⋆Assoc _ _ _)
      ∙ cong₂ (seq' 𝓒) refl (sym (G .F-seq [ e ]q [ e' ]q))
