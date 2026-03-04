-- Free category quotiented by equations

module Cubical.Categories.Instances.Presented where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base hiding (Id)
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Data.Sigma
open import Cubical.HITs.SetQuotients as SetQuotient
  renaming ([_] to [_]q) hiding (rec; elim)

open import Cubical.Categories.Instances.Quotient as CatQuotient
open import Cubical.Categories.Displayed.Instances.Weaken.Base as Weaken
open import Cubical.Categories.Instances.Quotient.More as CatQuotient
  hiding (elim)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓj : Level

open Category
open Functor
open NatIso hiding (sqRL; sqLL)
open NatTrans

module _ (𝓒 : Category ℓc ℓc') where
  record Axioms ℓj : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-suc ℓj)) where
    field
      equation : Type ℓj
      dom cod : equation → 𝓒 .ob
      lhs rhs : ∀ eq → 𝓒 [ dom eq , cod eq ]

  open Axioms
  mkAx : (Equation : Type ℓj) →
         (Equation →
           Σ[ A ∈ 𝓒 .ob ] Σ[ B ∈ 𝓒 .ob ] 𝓒 [ A , B ] × 𝓒 [ A , B ]) →
         Axioms ℓj
  mkAx Eq funs .equation = Eq
  mkAx Eq funs .dom eq = funs eq .fst
  mkAx Eq funs .cod eq = funs eq .snd .fst
  mkAx Eq funs .lhs eq = funs eq .snd .snd .fst
  mkAx Eq funs .rhs eq = funs eq .snd .snd .snd

  module QuoByAx (Ax : Axioms ℓj) where
    data _≈_ : ∀ {A B} → 𝓒 [ A , B ] → 𝓒 [ A , B ] →
               Type (ℓ-max (ℓ-max ℓc ℓc') ℓj) where
      ↑_ : ∀ eq → Ax .lhs eq ≈ Ax .rhs eq
      reflₑ : ∀ {A B} → (e : 𝓒 [ A , B ]) → e ≈ e
      ⋆ₑ-cong : ∀ {A B C}
           → (e e' : 𝓒 [ A , B ]) → (e ≈ e')
           → (f f' : 𝓒 [ B , C ]) → (f ≈ f')
           → (e ⋆⟨ 𝓒 ⟩ f) ≈ (e' ⋆⟨ 𝓒 ⟩ f')
    PresentedCat : Category _ _
    PresentedCat = QuotientCategory 𝓒 _≈_ reflₑ ⋆ₑ-cong

    ToPresented = QuoFunctor 𝓒 _≈_ reflₑ ⋆ₑ-cong

    isFullToPresented : isFull ToPresented
    isFullToPresented A B = []surjective

    ηEq : ∀ eq → Path (PresentedCat [ Ax .dom eq , Ax .cod eq ])
                      [ Ax .lhs eq ]q
                      [ Ax .rhs eq ]q
    ηEq eq = eq/ _ _ (↑ eq)

    module _ (𝓓 : Categoryᴰ PresentedCat ℓd ℓd') where
      private
        𝓓' = CatQuotient.ReindexQuo.reindex 𝓒 _≈_ reflₑ ⋆ₑ-cong 𝓓
        module 𝓓 = Categoryᴰ 𝓓
        module R = HomᴰReasoning 𝓓

      open Section
      elim : (F : GlobalSection 𝓓')
           → (∀ eq →
             PathP (λ i → 𝓓.Hom[ ηEq eq i ][
                                 F .F-obᴰ (Ax .dom eq)
                               , F .F-obᴰ (Ax .cod eq) ])
                   (F .F-homᴰ (Ax .lhs eq))
                   (F .F-homᴰ (Ax .rhs eq)))
           → GlobalSection 𝓓
      elim F F-respects-axioms =
        CatQuotient.elim 𝓒 _≈_ reflₑ ⋆ₑ-cong 𝓓 F
          (λ _ _ → F-respects-≈) where
        F-respects-≈ : {x y : 𝓒 .ob} {f g : Hom[ 𝓒 , x ] y}
          (p : f ≈ g) →
          PathP
          (λ i → 𝓓.Hom[ eq/ f g p i ][
            F .F-obᴰ x
          , F .F-obᴰ y ])
          (F .F-homᴰ f)
          (F .F-homᴰ g)
        F-respects-≈ (↑ eq) = F-respects-axioms eq
        F-respects-≈ {x}{y} (reflₑ f) = R.rectify {p = refl} refl
        F-respects-≈ (⋆ₑ-cong e e' p f f' q) =
          R.rectify
          (F .F-seqᴰ e f ◁
          (λ i → F-respects-≈ p i 𝓓.⋆ᴰ F-respects-≈ q i)
          ▷ (sym (F .F-seqᴰ e' f')))

    module _ (𝓓 : Category ℓd ℓd') (F : Functor 𝓒 𝓓)
        (F-satisfies-axioms : ∀ eq → F ⟪ Ax .lhs eq ⟫ ≡ F ⟪ Ax .rhs eq ⟫)
        where
      rec : Functor PresentedCat 𝓓
      rec = Weaken.introS⁻ (elim _ F' F-satisfies-axioms) where
        -- There's probably a general principle but η expansion is
        -- easier
        F' : GlobalSection _
        F' .Section.F-obᴰ = F .F-ob
        F' .Section.F-homᴰ = F .F-hom
        F' .Section.F-idᴰ = F .F-id
        F' .Section.F-seqᴰ = F .F-seq
