{-# OPTIONS --prop --lossy-unification #-}
module Gluing.CBPV.Pure.Multiplicative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Prop

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Sets
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.Sets
open import Cubical.Categories.Displayed.Instances.Codomain.Sets
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.Pure.Multiplicative

open Category
open Functor
open Functorᴰ
open Section

private
  variable
    ℓ ℓ' : Level

module MultiplicativeGluing
  (BaseTy : Kind → Type ℓ)
  (Fun : ∀ {k1 k2} → ≤Kind k1 k2
    → CBPV.Ob BaseTy k1 → CBPV.Ob BaseTy k2 → Type ℓ')
  (𝟙 : BaseTy 𝓥)
  where
  open CBPV BaseTy
  open Terms Fun

  private
    L = ℓ-max ℓ ℓ'

  pts : Functorⱽ CBPV (SetCBPV L)
  pts = points CBPV (gen 𝟙)

  module FundLem
    (ı-Ob : ∀ {k} (X : BaseTy k)
      → Tm {k1 = 𝓥} {k2 = k} tt (gen {k = 𝓥} 𝟙) (gen {k = k} X)
      → hSet L)
    where
    LR : ∀ {k} (Γ : Ob k) → Tm tt (gen 𝟙) Γ → hSet L
    LR = LocalElim.local-obᴰ pts (SetCBPVCodⱽ L) ⦃ SetCBPVCodReind L ⦄ ı-Ob

    module _
      (ı-Fun : ∀ {k1 k2 Γ Δ}{k≤ : ≤Kind k1 k2} (f : Fun k≤ Γ Δ)
        → ∀ (M : Tm tt (gen 𝟙) Γ)
        → ⟨ LR Γ M ⟩ → ⟨ LR Δ (seqS M (gen f)) ⟩)
      where
      fund-lemma : Section (∫F pts) (SetCBPVCod L)
      fund-lemma =
        LocalElim.localElim pts (SetCBPVCodⱽ L) ⦃ SetCBPVCodReind L ⦄ ı-Ob
          λ f → mk L λ z → (_ , ı-Fun f (z .fst) (z .snd)) , refl

      canonical : ∀ (M : Tm tt (gen 𝟙) Γ)
        → ⟨ LR (gen 𝟙) idS ⟩ → Fib L {Y = _ , isSetTm} (LR Γ) M
      canonical M lem .fst =
        pt L (fund-lemma .F-homᴰ (_ , M)) (idS , lem) .fst
      canonical M lem .snd =
        pt L (fund-lemma .F-homᴰ (_ , M)) (idS , lem) .snd ∙ IdLS M

      corollary : ∀ (M : Tm tt (gen 𝟙) Γ)
        → ⟨ LR (gen 𝟙) idS ⟩ → ⟨ LR Γ M ⟩
      corollary M lem = subst (λ M → ⟨ LR _ M ⟩) (c .snd) (c .fst .snd)
        where c = canonical M lem

module EZ-Can where
  data BaseTy : Kind → Type ℓ-zero where
    𝟙 Ans : BaseTy 𝓥

  open CBPV BaseTy

  data FUN : ∀ {k1 k2} → ≤Kind k1 k2
    → Ob k1 → Ob k2 → Type ℓ-zero where
    true false : FUN {k1 = 𝓥} {k2 = 𝓥} tt
      (gen {k = 𝓥} 𝟙) (gen {k = 𝓥} Ans)

  open Terms FUN

  tru fls : Tm {k1 = 𝓥} {k2 = 𝓥} tt
    (gen {k = 𝓥} 𝟙) (gen {k = 𝓥} Ans)
  tru = gen true
  fls = gen false

  Canonical : ∀ {k} (X : BaseTy k)
    → Tm {k1 = 𝓥} {k2 = k} tt
        (gen {k = 𝓥} 𝟙) (gen {k = k} X)
    → Type ℓ-zero
  Canonical 𝟙 V = V ≡ idS
  Canonical Ans V = (V ≡ tru) ⊎ (V ≡ fls)

  hCanonical : ∀ {k} (X : BaseTy k)
    → Tm {k1 = 𝓥} {k2 = k} tt
        (gen {k = 𝓥} 𝟙) (gen {k = k} X)
    → hSet ℓ-zero
  hCanonical X V .fst = Canonical X V
  hCanonical 𝟙 V .snd = isProp→isSet (isSetTm _ _)
  hCanonical Ans V .snd =
    isSet⊎ (isProp→isSet (isSetTm _ _)) (isProp→isSet (isSetTm _ _))

  module G = MultiplicativeGluing BaseTy FUN 𝟙

  open G.FundLem
    (λ {k} X M → hCanonical {k} X M)

  private
    [ret]' : Tm tt (gen Ans) ([F] (gen Ans))
    [ret]' = CartesianLiftNotation.πⱽ (CBPV ^opᴰ)
      (MultCBPV .snd .snd (gen Ans))

    [ret]'≡ret : [ret]' ≡ [ret]
    [ret]'≡ret = cong snd
      (CBPV^op.reind-filler⁻ _
      ∙ CBPV^op.≡in {pth = refl} (IdRS [ret]))

  FCanonical→Canonical :
    ∀ {M : Tm tt (gen 𝟙) ([F] (gen Ans))}
    → Fib ℓ-zero {Y = _ , isSetTm} (LR ([F] (gen Ans))) M
    → (M ≡ seqS tru [ret]) ⊎ (M ≡ seqS fls [ret])
  FCanonical→Canonical ((_ , ((V , inl V≡tru) , retV≡e)) , e≡M) =
    inl (sym (retV≡e ∙ e≡M) ∙ cong₂ seqS V≡tru [ret]'≡ret)
  FCanonical→Canonical ((_ , ((V , inr V≡fls) , retV≡e)) , e≡M) =
    inr (sym (retV≡e ∙ e≡M) ∙ cong₂ seqS V≡fls [ret]'≡ret)

  AllCanonical : ∀ ((_ , M) :
    (∫C (MultCBPV .fst)) [ (𝓥 , gen 𝟙) , (𝓒 , [F] (gen Ans)) ])
    → (M ≡ seqS tru [ret]) ⊎ (M ≡ seqS fls [ret])
  AllCanonical (_ , M) = FCanonical→Canonical $ canonical
    (λ { true V V≡id → inl (cong₂ seqS V≡id refl ∙ IdLS tru)
       ; false V V≡id → inr (cong₂ seqS V≡id refl ∙ IdLS fls)
       })
    M
    refl

private
  module Examples where
    open EZ-Can
    open CBPV BaseTy
    open Terms FUN

    isInl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ⊎ B → Bool
    isInl (inl _) = true
    isInl (inr _) = false

    _ : isInl (AllCanonical (_ , seqS tru [ret])) ≡ true
    _ = refl

    _ : isInl (AllCanonical (_ , seqS fls (seqS [ret] ([bind] [ret]))))
      ≡ false
    _ = refl

    _ : isInl (AllCanonical (_ , seqS ([thunk] (seqS tru [ret])) [force]))
      ≡ true
    _ = refl
