{-# OPTIONS --prop --lossy-unification #-}
module Gluing.CBPV.StateAlg.Multiplicative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

open import Cubical.Prop

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Sigma

open import Cubical.Algebra.State
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞; ≤Vertex to ≤Kind)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.StateAlgEnrichment
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.StateAlg
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.BoolState.Multiplicative

open Category
open Functor
open Functorᴰ
open Section

private
  variable
    ℓ ℓ' : Level

module StateAlgGluing
  (BaseTy : Kind → Type ℓ)
  (Fun : ∀ {k1 k2} → ≤Kind k1 k2
    → CBPV.Ob BaseTy k1 → CBPV.Ob BaseTy k2 → Type ℓ')
  (𝟙 : BaseTy 𝒱)
  where
  open CBPV BaseTy
  open Terms Fun

  private
    L = ℓ-max ℓ ℓ'

  pts : Functorⱽ CBPV (StateAlgCBPV {ℓ = L} .fst)
  pts = points CBPV CBPVState (gen 𝟙)

  ptsPreservesState :
    PreservesStateAlgEnrichment pts CBPVState StateAlgCBPVState
  ptsPreservesState = pointsPreservesState CBPV CBPVState (gen 𝟙)

module BoolStateSyntax where
  data BaseTy : Kind → Type ℓ-zero where
    𝟙 BoolTy : BaseTy 𝒱

  open CBPV BaseTy

  data FUN : ∀ {k1 k2} → ≤Kind k1 k2
    → Ob k1 → Ob k2 → Type ℓ-zero where
    true false : FUN tt (gen 𝟙) (gen BoolTy)

  open Terms FUN public

  tru fls : Tm tt (gen 𝟙) (gen BoolTy)
  tru = gen true
  fls = gen false

  quoteBool : Bool → Tm tt (gen 𝟙) (gen BoolTy)
  quoteBool false = fls
  quoteBool true = tru

  BaseRelation : ∀ {k} (X : BaseTy k)
    → Tm {k1 = 𝒱} tt (gen 𝟙) (gen X) → Type ℓ-zero
  BaseRelation 𝟙 V = V ≡ idS
  BaseRelation BoolTy V = Σ[ b ∈ Bool ] V ≡ quoteBool b

  hBaseRelation : ∀ {k} (X : BaseTy k)
    → Tm {k1 = 𝒱} tt (gen 𝟙) (gen X) → hSet ℓ-zero
  hBaseRelation X V .fst = BaseRelation X V
  hBaseRelation 𝟙 V .snd = isProp→isSet (isSetTm _ _)
  hBaseRelation BoolTy V .snd =
    isSetΣ isSetBool (λ _ → isProp→isSet (isSetTm _ _))

  module G = StateAlgGluing BaseTy FUN 𝟙

  module Fundamental = LocalElim
    G.pts
    (StateAlgCodⱽ ℓ-zero)
    StateAlgCBPVState
    G.ptsPreservesState
    (StateAlgCodState ℓ-zero)
    ⦃ StateAlgCodReind ℓ-zero ⦄

  baseObject : ∀ {k} (X : BaseTy k)
    → Categoryᴰ.ob[_] (StateAlgCod ℓ-zero)
        (k , G.pts .F-obᴰ (gen X))
  baseObject 𝟙 = hBaseRelation 𝟙
  baseObject BoolTy = hBaseRelation BoolTy

  fundamentalLemma :
    Section (∫F G.pts) (StateAlgCod ℓ-zero)
  fundamentalLemma =
    Fundamental.localElim baseObject λ where
      true → (ı tt , λ z → seqS (z .fst) tru , true
        , cong₂ seqS (z .snd) refl ∙ IdLS tru) , refl
      false → (ı tt , λ z → seqS (z .fst) fls , false
        , cong₂ seqS (z .snd) refl ∙ IdLS fls) , refl

  LogicalRelation : ∀ {k} (Γ : Ob k)
    → Tm tt (gen 𝟙) Γ → hSet ℓ-zero
  LogicalRelation {k = 𝒱} Γ = Fundamental.local-obᴰ baseObject Γ
  LogicalRelation {k = 𝒞} Γ = Fundamental.local-obᴰ baseObject Γ .fst

  canonical : ∀ {k} {Γ : Ob k} (M : Tm tt (gen 𝟙) Γ)
    → Σ[ w ∈ Σ _ (λ N → ⟨ LogicalRelation Γ N ⟩) ] w .fst ≡ M
  canonical {k = 𝒱} M =
    run .fst .snd (idS , refl) , (λ i → run .snd i .snd (idS , refl)) ∙ IdLS M
    where run = fundamentalLemma .F-homᴰ (_ , M)
  canonical {k = 𝒞} M =
    run .fst .snd (idS , refl) , (λ i → run .snd i .snd (idS , refl)) ∙ IdLS M
    where run = fundamentalLemma .F-homᴰ (_ , M)

  fundamentalAt : ∀ {k} {Γ : Ob k} (M : Tm tt (gen 𝟙) Γ)
    → ⟨ LogicalRelation Γ M ⟩
  fundamentalAt {Γ = Γ} M =
    subst (λ N → ⟨ LogicalRelation Γ N ⟩) (canonical M .snd)
      (canonical M .fst .snd)

  private
    [ret]' : Tm tt (gen BoolTy) ([F] (gen BoolTy))
    [ret]' = CartesianLiftNotation.πⱽ (CBPV ^opᴰ)
      (MultCBPV .snd .snd (gen BoolTy))

    [ret]'≡ret : [ret]' ≡ [ret]
    [ret]'≡ret = cong snd
      (CBPV^op.reind-filler⁻ _
      ∙ CBPV^op.≡in {pth = refl} (IdRS [ret]))

  RawFBool : Tm tt (gen 𝟙) ([F] (gen BoolTy)) → Type ℓ-zero
  RawFBool M =
    Σ[ (s , [ret]⟨s⟩≡M) ∈ fiber
      (recFSA-f
        (Tm tt (gen 𝟙) (gen BoolTy))
        (StateAlgEff (gen 𝟙) ([F] (gen BoolTy)))
        (λ V → seqS V [ret]'))
      M ]
      (∀ b → Σ[ q ∈ Bool ] s b .snd ≡ quoteBool q)

  raw-FBool : ∀ M → RawFBool M
  raw-FBool M .fst .fst = canonical M .fst .snd .fst .fst
  raw-FBool M .fst .snd = canonical M .fst .snd .fst .snd ∙ canonical M .snd
  raw-FBool M .snd = canonical M .fst .snd .snd

  interpretFreeStateBool :
    ⟨ FreeStateAlgebra (Bool , isSetBool) .fst ⟩
    → Tm tt (gen 𝟙) ([F] (gen BoolTy))
  interpretFreeStateBool = recFSA-f Bool
    (StateAlgEff (gen 𝟙) ([F] (gen BoolTy)))
    (λ b → seqS (quoteBool b) [ret])

  private
    rawState : ∀ {M} → RawFBool M
      → Bool → Bool × Tm tt (gen 𝟙) (gen BoolTy)
    rawState raw = raw .fst .fst

    rawRelated : ∀ {M} (raw : RawFBool M) b
      → Σ[ q ∈ Bool ] rawState raw b .snd ≡ quoteBool q
    rawRelated raw = raw .snd

    realizeRaw : ∀ {M} (raw : RawFBool M)
      → fiber interpretFreeStateBool M
    realizeRaw raw .fst b .fst = rawState raw b .fst
    realizeRaw raw .fst b .snd = rawRelated raw b .fst
    realizeRaw raw .snd =
      -- this would be a one-liner if not for the reind in [ret]'.
      cong₂ [rd]
        (cong ([wt] (rawState raw true .fst))
          (cong₂ seqS
            (sym (rawRelated raw true .snd)) (sym [ret]'≡ret)))
        (cong ([wt] (rawState raw false .fst))
          (cong₂ seqS
            (sym (rawRelated raw false .snd)) (sym [ret]'≡ret)))
      ∙ raw .fst .snd

  closed-FBool-surjective : ∀ M →
    fiber interpretFreeStateBool M
  closed-FBool-surjective M = realizeRaw (raw-FBool M)

  unquote-FBool : Tm _ (gen 𝟙) ([F] (gen BoolTy)) → ⟨ FreeStateAlgebra (Bool , isSetBool) .fst ⟩
  unquote-FBool M = closed-FBool-surjective M .fst

open BoolStateSyntax public

private
  module Examples where
    _ : unquote-FBool (seqS tru [ret]) true ≡ (true , true)
    _ = refl

    _ : unquote-FBool
      ([rd] ([wt] false (seqS tru [ret])) ([wt] true (seqS fls [ret]))) true
      ≡ (false , true)
    _ = refl

    _ : unquote-FBool ([wt] true (seqS fls [ret])) false ≡ (true , false)
    _ = refl
