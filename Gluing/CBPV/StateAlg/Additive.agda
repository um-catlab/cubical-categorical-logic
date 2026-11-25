-- Canonicity for Full Multiplicative Additive Unary CBPV with a state effect
{-# OPTIONS --prop --lossy-unification #-}
module Gluing.CBPV.StateAlg.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

open import Cubical.Prop

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

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
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.StateAlgEnrichment
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.StateAlg
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.BoolState.Additive

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
  (I : CBPV.Ob BaseTy 𝒱)
  where
  open CBPV BaseTy
  open Terms Fun

  private
    L = ℓ-max ℓ ℓ'

  pts : Functorⱽ (AddCBPV .fst .fst) (StateAlgCBPV {ℓ = L} .fst)
  pts = points (AddCBPV .fst .fst) CBPVState I

  ptsPreservesState :
    PreservesStateAlgEnrichment pts CBPVState StateAlgCBPVState
  ptsPreservesState = pointsPreservesState CBPV CBPVState I

module BoolStateSyntax where
  data BaseTy (k : Kind) : Type ℓ-zero where

  open CBPV BaseTy

  data FUN : ∀ {k1 k2} → ≤Kind k1 k2
    → Ob k1 → Ob k2 → Type ℓ-zero where

  open Terms FUN public

  UnitTy BoolTy : VTy
  UnitTy = [1]
  BoolTy = UnitTy [+] UnitTy

  private
    inl' inr' : Tm tt UnitTy BoolTy
    inl' = [+I1]
    inr' = [+I2]

  tru fls : Tm tt UnitTy BoolTy
  tru = inl'
  fls = inr'

  quoteBool : Bool → Tm tt UnitTy BoolTy
  quoteBool false = fls
  quoteBool true = tru

  module G = StateAlgGluing BaseTy FUN UnitTy

  module Fundamental = LocalElim
    G.pts
    (StateAlgCodAddⱽ ℓ-zero)
    StateAlgCBPVState
    G.ptsPreservesState
    (StateAlgCodState ℓ-zero)
    ⦃ StateAlgCodReind ℓ-zero ⦄

  baseObject : ∀ {k} (X : BaseTy k)
    → Categoryᴰ.ob[_] (StateAlgCod ℓ-zero)
        (k , G.pts .F-obᴰ (gen X))
  baseObject ()

  fundamentalLemma :
    Section (∫F G.pts) (StateAlgCod ℓ-zero)
  fundamentalLemma =
    Fundamental.localElim baseObject λ ()

  LogicalRelation : ∀ {k} (Γ : Ob k)
    → Tm tt UnitTy Γ → hSet ℓ-zero
  LogicalRelation {k = 𝒱} Γ = Fundamental.local-obᴰ baseObject Γ
  LogicalRelation {k = 𝒞} Γ = Fundamental.local-obᴰ baseObject Γ .fst

  canonical : ∀ {k} {Γ : Ob k} (M : Tm tt UnitTy Γ)
    → Σ[ w ∈ Σ _ (λ N → ⟨ LogicalRelation Γ N ⟩) ] w .fst ≡ M
  canonical {k = 𝒱} M =
    run .fst .snd (idS , tt*) , (λ i → run .snd i .snd (idS , tt*)) ∙ IdLS M
    where run = fundamentalLemma .F-homᴰ (_ , M)
  canonical {k = 𝒞} M =
    run .fst .snd (idS , tt*) , (λ i → run .snd i .snd (idS , tt*)) ∙ IdLS M
    where run = fundamentalLemma .F-homᴰ (_ , M)

  fundamentalAt : ∀ {k} {Γ : Ob k} (M : Tm tt UnitTy Γ)
    → ⟨ LogicalRelation Γ M ⟩
  fundamentalAt {Γ = Γ} M = subst (λ N → ⟨ LogicalRelation Γ N ⟩)
    (canonical M .snd) (canonical M .fst .snd)

  private
    [ret]' : Tm tt BoolTy ([F] BoolTy)
    [ret]' = CartesianLiftNotation.πⱽ (CBPV ^opᴰ)
      (MultCBPV .snd .snd BoolTy)

    [ret]'≡ret : [ret]' ≡ [ret]
    [ret]'≡ret = cong snd
      (Cop.reind-filler⁻ _
      ∙ Cop.≡in {pth = refl} (IdRS [ret]))

    value-σ₁≡[+I1] :
      BinProductⱽNotation.π₁ (CBPV ^opᴰ)
        (value-coproductⱽ UnitTy UnitTy) ≡ [+I1]
    value-σ₁≡[+I1] = Cop.rectifyOut {e' = refl}
      (Cop.reind-filler⁻ (Category.⋆IdR (KIND ^op) _)
      ∙ Cop.≡in {pth = refl} (IdRS [+I1]))

    value-σ₂≡[+I2] :
      BinProductⱽNotation.π₂ (CBPV ^opᴰ)
        (value-coproductⱽ UnitTy UnitTy) ≡ [+I2]
    value-σ₂≡[+I2] = Cop.rectifyOut {e' = refl}
      (Cop.reind-filler⁻ (Category.⋆IdR (KIND ^op) _)
      ∙ Cop.≡in {pth = refl} (IdRS [+I2]))

    CanonicalBool : Tm tt UnitTy BoolTy → Type ℓ-zero
    CanonicalBool V =
      fiber (λ (V₁ : Tm tt UnitTy UnitTy) → seqS V₁ inl') V
      ⊎ fiber (λ (V₂ : Tm tt UnitTy UnitTy) → seqS V₂ inr') V

    inspect-Bool : ∀ V → ⟨ LogicalRelation BoolTy V ⟩ → CanonicalBool V
    inspect-Bool V (inl ((V₁ , _) , p)) =
      inl (V₁ , sym (cong (seqS V₁) value-σ₁≡[+I1]) ∙ p)
    inspect-Bool V (inr ((V₂ , _) , p)) =
      inr (V₂ , sym (cong (seqS V₂) value-σ₂≡[+I2]) ∙ p)

    canonicalBool : ∀ V → ⟨ LogicalRelation BoolTy V ⟩
      → Σ[ b ∈ Bool ] V ≡ quoteBool b
    canonicalBool V related = Sum.rec
      (λ (V₁ , V₁-inl≡V) → true ,
        sym V₁-inl≡V
        ∙ cong (λ W → seqS W inl') ([1η] V₁ ∙ sym ([1η] idS))
        ∙ IdLS inl')
      (λ (V₂ , V₂-inr≡V) → false ,
        sym V₂-inr≡V
        ∙ cong (λ W → seqS W inr') ([1η] V₂ ∙ sym ([1η] idS))
        ∙ IdLS inr')
      (inspect-Bool V related)

  RawFBool : Tm tt UnitTy ([F] BoolTy) → Type ℓ-zero
  RawFBool M =
    Σ[ (s , [ret]⟨s⟩≡M) ∈ fiber
      (recFSA-f
        (Tm tt UnitTy BoolTy)
        (StateAlgEff UnitTy ([F] BoolTy))
        (λ V → seqS V [ret]'))
      M ]
      (∀ b → Σ[ q ∈ Bool ] s b .snd ≡ quoteBool q)

  raw-FBool : ∀ M → RawFBool M
  raw-FBool M .fst .fst = canonical M .fst .snd .fst .fst
  raw-FBool M .fst .snd = canonical M .fst .snd .fst .snd ∙ canonical M .snd
  raw-FBool M .snd b = canonicalBool _ (canonical M .fst .snd .snd b)

  interpretFreeStateBool :
    ⟨ FreeStateAlgebra (Bool , isSetBool) .fst ⟩
    → Tm tt UnitTy ([F] BoolTy)
  interpretFreeStateBool = recFSA-f Bool
    (StateAlgEff UnitTy ([F] BoolTy))
    (λ b → seqS (quoteBool b) [ret])

  private
    rawState : ∀ {M} → RawFBool M
      → Bool → Bool × Tm tt UnitTy BoolTy
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

  unquote-FBool : Tm _ UnitTy ([F] BoolTy)
    → ⟨ FreeStateAlgebra (Bool , isSetBool) .fst ⟩
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
