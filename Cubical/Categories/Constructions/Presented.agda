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
open import Cubical.HITs.SetQuotients as SetQuotient
  renaming ([_] to [_]q) hiding (rec; elim)

open import Cubical.Categories.Constructions.Quotient as CatQuotient
open import Cubical.Categories.Constructions.Free.Category.Quiver as Free
  hiding (rec; elim)
open import Cubical.Categories.Constructions.Quotient.More as CatQuotient
  hiding (elim)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Section

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓj : Level

open Category
open Functor
open NatIso hiding (sqRL; sqLL)
open NatTrans
open Quiver
open Interpᴰ

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
      reflₑ : ∀ {A B} → (e : FQ [ A , B ]) → e ≈ e
      ⋆ₑ-cong : ∀ {A B C}
           → (e e' : FQ [ A , B ]) → (e ≈ e')
           → (f f' : FQ [ B , C ]) → (f ≈ f')
           → (e ⋆⟨ FQ ⟩ f) ≈ (e' ⋆⟨ FQ ⟩ f')
      ⋆ₑIdL : ∀ {A B} (e : FQ [ A , B ]) → (idₑ ⋆ₑ e) ≈ e
      ⋆ₑIdR : ∀ {A B} (e : FQ [ A , B ]) → (e ⋆ₑ idₑ) ≈ e
      ⋆ₑAssoc : ∀ {A B C D} (e : FQ [ A , B ])
               (f : FQ [ B , C ])(g : FQ [ C , D ])
              → ((e ⋆ₑ f) ⋆ₑ g) ≈ (e ⋆ₑ (f ⋆ₑ g))

    PresentedCat : Category _ _
    PresentedCat = QuotientCategory FQ _≈_ reflₑ ⋆ₑ-cong

    FreeToPresented = QuoFunctor FQ _≈_ reflₑ ⋆ₑ-cong

    isFullFreeToPresented : isFull FreeToPresented
    isFullFreeToPresented A B = []surjective

    ηP : Interp Q PresentedCat
    ηP .I-ob = λ A → A
    ηP .I-hom = λ e → [ ↑ e ]q

    ηEq : ∀ eq → Path (PresentedCat [ Ax .dom eq , Ax .cod eq ])
                      [ Ax .lhs eq ]q
                      [ Ax .rhs eq ]q
    ηEq eq = eq/ _ _ (↑ eq)

    module _ (𝓓 : Categoryᴰ PresentedCat ℓc ℓc') where
      private
        𝓓' = reindexᴰQuo FQ _≈_ reflₑ ⋆ₑ-cong 𝓓
        module 𝓓 = Categoryᴰ 𝓓

      open Section
      elim : (F : Interpᴰ Q 𝓓')
           → (∀ eq →
             PathP (λ i → 𝓓.Hom[ ηEq eq i ][
                                 F .I-ob (Ax .dom eq)
                               , F .I-ob (Ax .cod eq) ])
                   (Free.elim Q F .F-hom (Ax .lhs eq))
                   (Free.elim Q F .F-hom (Ax .rhs eq)))
           → Section 𝓓
      elim F F-respects-axioms =
        CatQuotient.elim FQ _≈_ reflₑ ⋆ₑ-cong 𝓓
          (Free.elim Q F)
          (λ _ _ → F-respects-≈) where
        F-respects-≈ : {x y : FQ .ob} {f g : Hom[ FQ , x ] y}
          (p : f ≈ g) →
          PathP
          (λ i → 𝓓.Hom[ eq/ f g p i ][
            Free.elim Q F .F-ob x
          , Free.elim Q F .F-ob y ])
          (Free.elim Q F .F-hom f)
          (Free.elim Q F .F-hom g)
        F-respects-≈ (↑ eq) = F-respects-axioms eq
        F-respects-≈ {x}{y} (reflₑ f) = base-path-irr 𝓓 {p = refl} refl
        F-respects-≈ (⋆ₑ-cong e e' p f f' q) =
          base-path-irr 𝓓
          (Free.elim Q F .F-seq e f ◁
          (λ i → F-respects-≈ p i 𝓓.⋆ᴰ F-respects-≈ q i)
          ▷ (sym (Free.elim Q F .F-seq e' f')))
        F-respects-≈ (⋆ₑIdL g) = base-path-irr 𝓓 (𝓓.⋆IdLᴰ (elimF Q F g))
        F-respects-≈ {x}{y} (⋆ₑIdR g) = base-path-irr 𝓓 (𝓓.⋆IdRᴰ (elimF Q F g))
        F-respects-≈ (⋆ₑAssoc e f g) =
          base-path-irr 𝓓 (𝓓.⋆Assocᴰ (elimF Q F e) (elimF Q F f) (elimF Q F g))

    module _ (𝓒 : Category ℓc ℓc') (ı : Interp Q 𝓒) where
      Frec = Free.rec Q ı

      module _ (satisfies-axioms : ∀ eq →
        Frec ⟪ Ax .lhs eq ⟫ ≡ Frec ⟪ Ax .rhs eq ⟫) where
        rec-respects-≈ : ∀ {A B} {e e' : FQ [ A , B ]}
                       → e ≈ e'
                       → Frec ⟪ e ⟫ ≡ Frec ⟪ e' ⟫
        rec-respects-≈ (↑ eq) = satisfies-axioms eq
        rec-respects-≈ (reflₑ _) = refl
        rec-respects-≈ (⋆ₑ-cong e e' p f f' q) =
          Frec .F-seq e f
          ∙ cong₂ (seq' 𝓒) (rec-respects-≈ p) (rec-respects-≈ q)
          ∙ sym (Frec .F-seq e' f')
        rec-respects-≈ (⋆ₑIdL _) = 𝓒 .⋆IdL _
        rec-respects-≈ (⋆ₑIdR _) = 𝓒 .⋆IdR _
        rec-respects-≈ (⋆ₑAssoc e f g) = 𝓒 .⋆Assoc _ _ _

        rec : Functor PresentedCat 𝓒
        rec .F-ob = ı .I-ob
        rec .F-hom =
          SetQuotient.rec (𝓒 .isSetHom) (Frec .F-hom) (λ _ _ → rec-respects-≈)
        rec .F-id = refl
        rec .F-seq = elimProp2 (λ _ _ → 𝓒 .isSetHom _ _) (λ _ _ → refl)
