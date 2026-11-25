-- Canonicity for Full Multiplicative Additive Unary Pure CBPV
{-# OPTIONS --prop --lossy-unification #-}
module Gluing.CBPV.Pure.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Prop

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞; ≤Vertex to ≤Kind)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.CBPV.Unary.Additive
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Sets
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.Sets
open import Cubical.Categories.Displayed.Instances.Codomain.Sets
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.Pure.Additive

open Category
open Functor
open Functorᴰ
open Section

private
  variable
    ℓ ℓ' : Level

module AdditiveGluing
  (BaseTy : Kind → Type ℓ)
  (Fun : ∀ {k1 k2} → ≤Kind k1 k2
    → CBPV.Ob BaseTy k1 → CBPV.Ob BaseTy k2 → Type ℓ')
  (I : CBPV.Ob BaseTy 𝒱)
  where
  open CBPV BaseTy
  open Terms Fun

  private
    L = ℓ-max ℓ ℓ'

  pts : Functorⱽ (AddCBPV .fst .fst) (SetCBPV L)
  pts = points (AddCBPV .fst .fst) I

  module FundLem
    (ı-Ob : ∀ {k} (X : BaseTy k)
      → Tm {k₁ = 𝒱} {k₂ = k} tt I (gen {k = k} X)
      → hSet L)
    where
    LR : ∀ {k} (Γ : Ob k) → Tm tt I Γ → hSet L
    LR = LocalElim.local-obᴰ pts (SetAddCBPVCodⱽ L) ⦃ SetCBPVCodReind L ⦄ ı-Ob

    module _
      (ı-Fun : ∀ {k1 k2 Γ Δ}{k≤ : ≤Kind k1 k2} (f : Fun k≤ Γ Δ)
        → ∀ (M : Tm tt I Γ)
        → ⟨ LR Γ M ⟩ → ⟨ LR Δ (seqS M (gen f)) ⟩)
      where
      fund-lemma : Section (∫F pts) (SetCBPVCod L)
      fund-lemma =
        LocalElim.localElim pts (SetAddCBPVCodⱽ L) ⦃ SetCBPVCodReind L ⦄ ı-Ob
          λ f → mk L λ z → (_ , ı-Fun f (z .fst) (z .snd)) , refl

      canonical : ∀ {k} {Γ : Ob k} (M : Tm tt I Γ)
        → ⟨ LR I idS ⟩ → Fib L {Y = _ , isSetTm} (LR Γ) M
      canonical M lem .fst =
        pt L (fund-lemma .F-homᴰ (_ , M)) (idS , lem) .fst
      canonical M lem .snd =
        pt L (fund-lemma .F-homᴰ (_ , M)) (idS , lem) .snd ∙ IdLS M

      corollary : ∀ {k} {Γ : Ob k} (M : Tm tt I Γ)
        → ⟨ LR I idS ⟩ → ⟨ LR Γ M ⟩
      corollary M lem = subst (λ M → ⟨ LR _ M ⟩) (c .snd) (c .fst .snd)
        where c = canonical M lem

module EZ-Can where
  data BaseTy (k : Kind) : Type ℓ-zero where

  open CBPV BaseTy

  data FUN : ∀ {k1 k2} → ≤Kind k1 k2
    → Ob k1 → Ob k2 → Type ℓ-zero where

  open Terms FUN

  BoolTy : VTy
  BoolTy = [1] [+] [1]

  private
    inl' inr' : Tm tt [1] BoolTy
    inl' = [+I1]
    inr' = [+I2]

  tru fls : Tm tt [1] BoolTy
  tru = inl'
  fls = inr'

  module G = AdditiveGluing BaseTy FUN [1]

  open G.FundLem (λ ())

  LogicalRelation : ∀ {k} (Γ : Ob k) → Tm tt [1] Γ → hSet ℓ-zero
  LogicalRelation = LR

  fundamentalAt : ∀ {k} {Γ : Ob k} (M : Tm tt [1] Γ)
    → ⟨ LogicalRelation Γ M ⟩
  fundamentalAt M = corollary (λ ()) M tt*

  private
    [ret]' : Tm tt BoolTy ([F] BoolTy)
    [ret]' = CartesianLiftNotation.πⱽ (CBPV ^opᴰ)
      (MultCBPV .snd .snd BoolTy)

    [ret]'≡ret : [ret]' ≡ [ret]
    [ret]'≡ret = cong snd
      (Cop.reind-filler⁻ _
      ∙ Cop.≡in {pth = refl} (IdRS [ret]))

  RawFBool : Tm tt [1] ([F] BoolTy) → Type ℓ-zero
  RawFBool M = Fib ℓ-zero {Y = _ , isSetTm} (LogicalRelation ([F] BoolTy)) M

  raw-FBool : ∀ M → RawFBool M
  raw-FBool M = canonical (λ ()) M tt*

  private
    value-σ₁≡[+I1] :
      BinProductⱽNotation.π₁ (CBPV ^opᴰ)
        (value-coproductⱽ [1] [1]) ≡ [+I1]
    value-σ₁≡[+I1] = Cop.rectifyOut {e' = refl}
      (Cop.reind-filler⁻ (Category.⋆IdR (KIND ^op) _)
      ∙ Cop.≡in {pth = refl} (IdRS [+I1]))

    value-σ₂≡[+I2] :
      BinProductⱽNotation.π₂ (CBPV ^opᴰ)
        (value-coproductⱽ [1] [1]) ≡ [+I2]
    value-σ₂≡[+I2] = Cop.rectifyOut {e' = refl}
      (Cop.reind-filler⁻ (Category.⋆IdR (KIND ^op) _)
      ∙ Cop.≡in {pth = refl} (IdRS [+I2]))

    CanonicalBool : Tm tt [1] BoolTy → Type ℓ-zero
    CanonicalBool V =
      fiber (λ (V₁ : Tm tt [1] [1]) → seqS V₁ inl') V
      ⊎ fiber (λ (V₂ : Tm tt [1] [1]) → seqS V₂ inr') V

    inspect-Bool : ∀ V → ⟨ LogicalRelation BoolTy V ⟩ → CanonicalBool V
    inspect-Bool V (inl ((V₁ , _) , p)) =
      inl (V₁ , sym (cong (seqS V₁) value-σ₁≡[+I1]) ∙ p)
    inspect-Bool V (inr ((V₂ , _) , p)) =
      inr (V₂ , sym (cong (seqS V₂) value-σ₂≡[+I2]) ∙ p)

  FCanonical→Canonical : ∀ {M} → RawFBool M
    → (M ≡ seqS tru [ret]) ⊎ (M ≡ seqS fls [ret])
  FCanonical→Canonical ((_ , ((V , related) , retV≡e)) , e≡M) = Sum.rec
    (λ (V₁ , V₁-inl≡V) → inl
      ( sym (retV≡e ∙ e≡M)
      ∙ cong₂ seqS
          ( sym V₁-inl≡V
          ∙ cong (λ W → seqS W inl') ([1η] V₁ ∙ sym ([1η] idS))
          ∙ IdLS inl')
          [ret]'≡ret))
    (λ (V₂ , V₂-inr≡V) → inr
      ( sym (retV≡e ∙ e≡M)
      ∙ cong₂ seqS
          ( sym V₂-inr≡V
          ∙ cong (λ W → seqS W inr') ([1η] V₂ ∙ sym ([1η] idS))
          ∙ IdLS inr')
          [ret]'≡ret))
    (inspect-Bool V related)

  AllCanonical : ∀ ((_ , M) :
    (∫C (AddCBPV .fst .fst)) [ (𝒱 , [1]) , (𝒞 , [F] BoolTy) ])
    → (M ≡ seqS tru [ret]) ⊎ (M ≡ seqS fls [ret])
  AllCanonical (_ , M) = FCanonical→Canonical (raw-FBool M)

private
  module Examples where
    open EZ-Can
    open CBPV BaseTy
    open Terms FUN

    isInl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ⊎ B → Bool
    isInl (inl _) = true
    isInl (inr _) = false

    _ : isInl (AllCanonical
      (_ , seqS fls ([+E] (seqS fls [ret]) (seqS tru [ret])))) ≡ true
    _ = refl

    _ : isInl (AllCanonical (_ , seqS ([×I] fls tru) (seqS [×π2] [ret])))
      ≡ true
    _ = refl

    _ : isInl (AllCanonical
      (_ , seqS ([&I] (seqS tru [ret]) (seqS fls [ret])) [&π2])) ≡ false
    _ = refl
