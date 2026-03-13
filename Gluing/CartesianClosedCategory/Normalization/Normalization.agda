{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.Normalization.Normalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver as PQ
open PQ using (×Quiver; module ×Quiver)
import Cubical.Categories.Instances.Free.CartesianCategory.Forded as FCC
import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded as FCCC
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.StrictHom


open import Gluing.CartesianClosedCategory.Normalization.Renamings as Ren
open import Gluing.CartesianClosedCategory.Normalization.NormalForms as NF

private
  variable ℓQ ℓQ' : Level

open Category
open Functor
open Categoryᴰ
open Section
open PshHom

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private
    module Q = ×⇒Quiver Q
    ℓ = ℓ-max ℓQ ℓQ'

    -- From Renamings
    |REN|' = Ren.|REN| Q
    ι' = Ren.ι Q
    ι-ob' = Ren.ι-ob Q
    |CCC| = Ren.|FREE-CCC| Q
    module |CCC| = Category |CCC|
    nerve' = Ren.nerve Q
    PSHᴰ' = Ren.PSHᴰ Q
    module PSHᴰ'' = Categoryᴰ PSHᴰ'
    PSHᴰCᴰ' = Ren.PSHᴰCᴰ Q
    PSHᴰCCCⱽ' = Ren.PSHᴰCartesianClosedⱽ Q
    nerve-bp' = Ren.nerve-pres-bp Q

    -- From NormalForms
    Nf' = NF.Nf Q
    Ne' = NF.Ne Q
    renNf' = NF.renNf Q
    renNe' = NF.renNe Q
    ⌈_⌉nf' = NF.⌈_⌉nf Q
    ⌈_⌉ne' = NF.⌈_⌉ne Q
    Ctx' = NF.Ctx Q
    Ty' = NF.Ty Q
    Ren'' = NF.Ren' Q
    renNf-id' = NF.renNf-id Q
    renNf-⋆' = NF.renNf-⋆ Q

  -- CCC composition and pairing
  private
    pair' : ∀ {Γ A B : Ty'}
      → |CCC| [ Γ , A ] → |CCC| [ Γ , B ] → |CCC| [ Γ , A × B ]
    pair' = FCCC.⟨_,_⟩' Q

    -- Pair naturality: ⟨ h ⋆ f , h ⋆ g ⟩ ≡ h ⋆ ⟨ f , g ⟩
    pairNat : ∀ {A B C D : Ty'}
      (h : |CCC| [ A , B ]) (f : |CCC| [ B , C ]) (g : |CCC| [ B , D ])
      → pair' (h |CCC|.⋆ f) (h |CCC|.⋆ g) ≡ h |CCC|.⋆ pair' f g
    pairNat h f g = sym (
      FCCC.×η Eq.refl (h |CCC|.⋆ pair' f g)
      ∙ cong₂ pair'
          (|CCC|.⋆Assoc h (pair' f g) (FCCC.π₁' Q)
            ∙ cong (h |CCC|.⋆_) FCCC.×β₁)
          (|CCC|.⋆Assoc h (pair' f g) (FCCC.π₂' Q)
            ∙ cong (h |CCC|.⋆_) FCCC.×β₂))

  -- ι preserves wkRen
  private
    ι-wk : ∀ {Δ Γ A} (σ : Ren'' Δ Γ)
      → ι' .F-hom (NF.wkRen Q {A = A} σ)
        ≡ pair' (FCCC.π₁' Q |CCC|.⋆ ι' .F-hom σ) (FCCC.π₂' Q)
    ι-wk σ = refl

    -- Lambda naturality: lam (⟨ π₁ ⋆ h , π₂ ⟩ ⋆ t) ≡ h ⋆ lam t
    lamNat : ∀ {Δ Γ A B} (h : |CCC| [ Δ , Γ ])
      (t : |CCC| [ Γ × A , B ])
      → FCCC.lam' Q (pair' (FCCC.π₁' Q |CCC|.⋆ h) (FCCC.π₂' Q) |CCC|.⋆ t)
        ≡ h |CCC|.⋆ FCCC.lam' Q t
    lamNat h t =
      cong (FCCC.lam' Q) body-eq
      ∙ sym (FCCC.λη Eq.refl (h |CCC|.⋆ FCCC.lam' Q t))
      where
        P = pair' (FCCC.π₁' Q |CCC|.⋆ h) (FCCC.π₂' Q)
        lmt = FCCC.lam' Q t
        body-eq : P |CCC|.⋆ t
          ≡ pair' (FCCC.π₁' Q |CCC|.⋆ (h |CCC|.⋆ lmt)) (FCCC.π₂' Q)
            |CCC|.⋆ FCCC.eval' Q
        body-eq =
          cong (P |CCC|.⋆_) (sym (FCCC.λβ Eq.refl t))
          ∙ sym (|CCC| .⋆Assoc P _ (FCCC.eval' Q))
          ∙ cong (|CCC|._⋆ FCCC.eval' Q)
            (sym (pairNat P (FCCC.π₁' Q |CCC|.⋆ lmt) (FCCC.π₂' Q))
              ∙ cong₂ pair'
                (sym (|CCC| .⋆Assoc P (FCCC.π₁' Q) lmt)
                  ∙ cong (|CCC|._⋆ lmt) FCCC.×β₁
                  ∙ |CCC| .⋆Assoc (FCCC.π₁' Q) h lmt)
                FCCC.×β₂)

  -- Renaming-embedding commutation (needed for OB .F-hom)
  mutual
    renNfCommutes : ∀ {Δ Γ A} (σ : Ren'' Δ Γ) (nf : Nf' Γ A)
      → ⌈ renNf' σ nf ⌉nf' ≡ ι' .F-hom σ ⋆⟨ |CCC| ⟩ ⌈ nf ⌉nf'
    renNfCommutes σ (neNf n) = renNeCommutes σ n
    renNfCommutes σ unitNf = sym (FCCC.⊤η Eq.refl _)
    renNfCommutes σ (pairNf a b) =
      cong₂ pair' (renNfCommutes σ a) (renNfCommutes σ b)
      ∙ pairNat (ι' .F-hom σ) ⌈ a ⌉nf' ⌈ b ⌉nf'
    renNfCommutes σ (lamNf {A} {B} t) =
      cong (FCCC.lam' Q) (renNfCommutes (NF.wkRen Q σ) t
        ∙ cong (|CCC|._⋆ ⌈ t ⌉nf') (ι-wk σ))
      ∙ lamNat (ι' .F-hom σ) ⌈ t ⌉nf'

    renNeCommutes : ∀ {Δ Γ A} (σ : Ren'' Δ Γ) (ne : Ne' Γ A)
      → ⌈ renNe' σ ne ⌉ne' ≡ ι' .F-hom σ ⋆⟨ |CCC| ⟩ ⌈ ne ⌉ne'
    renNeCommutes σ (varNe v) = ι' .F-seq σ v
    renNeCommutes σ (fstNe n) =
      cong (|CCC|._⋆ FCCC.π₁' Q) (renNeCommutes σ n)
      ∙ |CCC|.⋆Assoc _ _ _
    renNeCommutes σ (sndNe n) =
      cong (|CCC|._⋆ FCCC.π₂' Q) (renNeCommutes σ n)
      ∙ |CCC|.⋆Assoc _ _ _
    renNeCommutes σ (genNe e nf) =
      cong (|CCC|._⋆ FCCC.↑ₑ Q e) (renNfCommutes σ nf)
      ∙ |CCC|.⋆Assoc _ _ _
    renNeCommutes σ (appNe n a) =
      cong (|CCC|._⋆ FCCC.eval' Q)
        (cong₂ pair' (renNeCommutes σ n) (renNfCommutes σ a)
          ∙ pairNat (ι' .F-hom σ) ⌈ n ⌉ne' ⌈ a ⌉nf')
      ∙ |CCC|.⋆Assoc _ _ _

  -- Displayed presheaf of normal forms at base types
  OB : (a : Q.ob) → PSHᴰ''.ob[ nerve' ⟅ ↑ a ⟆ ]
  OB a .F-ob (Γ , _ , f) =
    (Σ[ nf ∈ Nf' Γ (↑ a) ] ⌈ nf ⌉nf' ≡ f) ,
    isSetΣ {!!}
      (λ _ → isSet→isGroupoid (|CCC| .isSetHom) _ _)
  OB a .F-hom {x = Γ , _ , f} {y = Δ , _ , f'} (σ , _ , eq) (nf , p) =
    renNf' σ nf ,
    renNfCommutes σ nf ∙ cong (λ x → ι' .F-hom σ ⋆⟨ |CCC| ⟩ x) p ∙ Eq.eqToPath eq
  OB a .F-id = funExt λ (nf , p) → ΣPathP (renNf-id' nf ,
    isSet→SquareP (λ _ _ → |CCC| .isSetHom) _ _ _ _)
  OB a .F-seq σ τ = funExt λ (nf , _) → ΣPathP (renNf-⋆' (τ .fst) (σ .fst) nf ,
    isSet→SquareP (λ _ _ → |CCC| .isSetHom) _ _ _ _)

  -- Motive and semantic type abbreviations
  private
    motive' = FCCC.elimLocalMotive Q (nerve' , nerve-bp') PSHᴰCCCⱽ'
    module Mot = CartesianClosedCategoryᴰ motive'

    elimOb' = FCCC.elimOb Q motive' OB
    REN-×Q' = Ren.REN-×Quiver Q

    -- Semantic type: what elimOb gives at (Γ, tt, f)
    Sem : (A : Ty') → (Γ : Ctx') → |CCC| [ ι-ob' Γ , A ] → Type ℓ
    Sem A Γ f = elimOb' A .F-ob (Γ , tt , f) .fst

  reify-arr : (A B : Ty')
    → (∀ {Γ f} → Sem B Γ f → Σ[ nf ∈ Nf' Γ B ] ⌈ nf ⌉nf' ≡ f)
    → (∀ {Γ} → (ne : Ne' Γ A) → Sem A Γ ⌈ ne ⌉ne')
    → ∀ {Γ f} → Sem (A ⇒ B) Γ f → Σ[ nf ∈ Nf' Γ (A ⇒ B) ] ⌈ nf ⌉nf' ≡ f
  reify-arr A B reifyB reflectA {Γ} {f} x =
    let Γ' = Γ PQ.× (PQ.↑ A)
        x' = elimOb' (A ⇒ B) .F-hom
          (FCC.π₁' REN-×Q' , tt , Eq.refl) x
        v = reflectA (varNe (FCC.π₂' REN-×Q'))
        g = pair' (FCCC.π₁' Q |CCC|.⋆ f) (FCCC.π₂' Q)
        x'' = subst (Sem (A ⇒ B) Γ') (sym FCCC.×β₁) x'
        v' = subst (Sem A Γ') (sym FCCC.×β₂) v
        body = Mot.appᴰ .N-ob (Γ' , tt , g) (x'' , v')
        nfB = reifyB body .fst
        pB = reifyB body .snd
    in lamNf nfB , cong (FCCC.lam' Q) pB ∙ sym (FCCC.λη Eq.refl f)

  reflect-arr : (A B : Ty')
    → (∀ {Γ f} → Sem A Γ f → Σ[ nf ∈ Nf' Γ A ] ⌈ nf ⌉nf' ≡ f)
    → (∀ {Γ} → (ne : Ne' Γ B) → Sem B Γ ⌈ ne ⌉ne')
    → ∀ {Γ} → (ne : Ne' Γ (A ⇒ B)) → Sem (A ⇒ B) Γ ⌈ ne ⌉ne'
  -- this is whats slow
  reflect-arr A B reifyA reflectB {Γ} ne = {!!}
    -- pshhom {!!} {!!}
    -- the holes here have huge goals

  -- Reify and reflect (quote/unquote) by induction on types
  reify : (A : Ty') → ∀ {Γ f} → Sem A Γ f
    → Σ[ nf ∈ Nf' Γ A ] ⌈ nf ⌉nf' ≡ f
  reflect : (A : Ty') → ∀ {Γ} → (ne : Ne' Γ A)
    → Sem A Γ ⌈ ne ⌉ne'
  reify (↑ a) x = x
  reify ⊤ x = unitNf , sym (FCCC.⊤η Eq.refl _)
  reify (A × B) (xa , xb) =
    let (nfa , pa) = reify A xa
        (nfb , pb) = reify B xb
    in pairNf nfa nfb , cong₂ pair' pa pb ∙ sym (FCCC.×η Eq.refl _)
  reify (A ⇒ B) x = reify-arr A B (reify B) (reflect A) x

  reflect (↑ a) ne = neNf ne , refl
  reflect ⊤ ne = lift tt
  reflect (A × B) ne = reflect A (fstNe ne) , reflect B (sndNe ne)
  reflect (A ⇒ B) ne = reflect-arr A B (reify A) (reflect B) ne

  -- Section construction
  S : Section nerve' PSHᴰCᴰ'
  S = FCCC.elimLocal Q (nerve' , nerve-bp') PSHᴰCCCⱽ'
       (FCCC.mkElimInterpᴰ OB
         λ e → record
           { N-ob = λ { (Γ , _ , f) x →
               let (nf , p) = reify (Q.dom e) x
                   ne = genNe e nf
               -- Try to avoid subst here?
               in subst (Sem (Q.cod e) Γ)
                    (cong (|CCC|._⋆ FCCC.↑ₑ Q e) p) (reflect (Q.cod e) ne) }
           ; N-hom = λ c c' f x → {!!} })

  normalize : ∀ {Γ A} → |CCC|.Hom[ Γ , A ] → Nf Q (PQ.↑ Γ) A
  normalize e = {!S .F-homᴰ ? .N-ob ? ? ?!}
