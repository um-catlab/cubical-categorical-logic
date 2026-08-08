{-# OPTIONS --prop --lossy-unification #-}
module Gluing.CBPV.Algebra.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Prop

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

open import Cubical.Algebra.Signature.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞;
    ≤Vertex to ≤Kind)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
  renaming (Section to DisplayedSection)
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Algebra
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Algebra.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Algebra.Additive
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.AlgEnriched.Additive
open import Cubical.Categories.Displayed.Instances.Algebra.Algebra

open Category
open Functor
open Functorᴰ
open DisplayedSection

private
  variable
    ℓO ℓA : Level

module AlgebraGluing
  (Sig : Signature ℓO ℓA)
  (isSetOp : isSet (Signature.Op Sig))
  (BaseTy : Kind → Type (AlgebraLevel Sig))
  (Fun : ∀ {k₁ k₂} → ≤Kind k₁ k₂
    → CBPV.Ob Sig BaseTy k₁ → CBPV.Ob Sig BaseTy k₂
    → Type (AlgebraLevel Sig))
  (I : CBPV.Ob Sig BaseTy 𝒱)
  where
  open CBPV Sig BaseTy
  open Terms Fun

  pts : Functorⱽ (AddCBPV .fst .fst)
    (AlgebraAddCBPV Sig isSetOp .fst .fst)
  pts = points Sig isSetOp (AddCBPV .fst .fst) CBPVAlg I

  ptsPreservesAlgebra : PreservesAlgebraEnrichment Sig pts
    CBPVAlg (AlgebraCBPVAlg Sig isSetOp)
  ptsPreservesAlgebra =
    pointsPreservesAlgebra Sig isSetOp (AddCBPV .fst .fst) CBPVAlg I

module BoolAlgebraSyntax
  (Sig : Signature ℓO ℓA)
  (isSetOp : isSet (Signature.Op Sig))
  where
  open Signature Sig

  private
    L = AlgebraLevel Sig

  data BaseTy (k : Kind) : Type L where

  open CBPV Sig BaseTy

  data FUN : ∀ {k₁ k₂} → ≤Kind k₁ k₂
    → Ob k₁ → Ob k₂ → Type L where

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

  module G = AlgebraGluing Sig isSetOp BaseTy FUN UnitTy

  module Fundamental = LocalElim
    G.pts
    (AlgebraAddCBPVⱽ Sig isSetOp)
    (AlgebraCBPVAlg Sig isSetOp)
    G.ptsPreservesAlgebra
    (AlgebraCBPVAlgᴰ Sig isSetOp)

  baseObject : ∀ {k} (X : BaseTy k)
    → Categoryᴰ.ob[_] (AlgebraAddCBPVⱽ Sig isSetOp .fst .fst)
        (k , G.pts .F-obᴰ (gen X))
  baseObject ()

  fundamentalLemma :
    DisplayedSection (∫F G.pts) (AlgebraAddCBPVⱽ Sig isSetOp .fst .fst)
  fundamentalLemma = Fundamental.localElim baseObject λ ()

  LogicalRelation : ∀ {k} (Γ : Ob k)
    → Tm tt UnitTy Γ → hSet L
  LogicalRelation {k = 𝒱} Γ = Fundamental.local-obᴰ baseObject Γ
  LogicalRelation {k = 𝒞} Γ = Fundamental.local-obᴰ baseObject Γ .fst

  fundamentalAt : ∀ {k} {Γ : Ob k} (M : Tm tt UnitTy Γ)
    → ⟨ LogicalRelation Γ M ⟩
  fundamentalAt {k = 𝒱} {Γ = Γ} M = subst
    (λ N → ⟨ LogicalRelation Γ N ⟩)
    (IdLS M) $
    fundamentalLemma .F-homᴰ (_ , M) idS tt*
  fundamentalAt {k = 𝒞} {Γ = Γ} M = subst
    (λ N → ⟨ LogicalRelation Γ N ⟩)
    (IdLS M) $
    fundamentalLemma .F-homᴰ (_ , M) idS tt*

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

    CanonicalBool : Tm tt UnitTy BoolTy → Type L
    CanonicalBool V =
      fiber (λ (V₁ : Tm tt UnitTy UnitTy) → seqS V₁ inl') V
      ⊎ fiber (λ (V₂ : Tm tt UnitTy UnitTy) → seqS V₂ inr') V

    inspect-Bool : ∀ V → ⟨ LogicalRelation BoolTy V ⟩ → CanonicalBool V
    inspect-Bool V (inl (V₁ , p , _)) =
      inl (V₁ , sym (cong (seqS V₁) value-σ₁≡[+I1]) ∙ p)
    inspect-Bool V (inr (V₂ , p , _)) =
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

  RawFBool : Tm tt UnitTy ([F] BoolTy) → Type L
  RawFBool M = ⟨ LogicalRelation ([F] BoolTy) M ⟩

  raw-FBool : ∀ M → RawFBool M
  raw-FBool = fundamentalAt

  interpretFreeBool :
    FreeAlgebra Bool .fst → Tm tt UnitTy ([F] BoolTy)
  interpretFreeBool = recFA
    (_ , AlgebraEff UnitTy ([F] BoolTy))
    (λ b → seqS (quoteBool b) [ret]) .fst

  private
    rawTerm : ∀ {M} → RawFBool M
      → |FreeAlgebra| (Tm tt UnitTy BoolTy)
    rawTerm raw = raw .fst

    rawRelated : ∀ {M} (raw : RawFBool M)
      → |FreeAlgebraᴰ|
          (λ V → ⟨ LogicalRelation BoolTy V ⟩)
          (rawTerm raw)
    rawRelated raw = raw .snd .snd

    rawEquation : ∀ {M} (raw : RawFBool M)
      → recFA (_ , AlgebraEff UnitTy ([F] BoolTy))
          (λ V → seqS V [ret]') .fst (rawTerm raw) ≡ M
    rawEquation raw = raw .snd .fst

    rawRec : Homo
      (FreeAlgebra (Tm tt UnitTy BoolTy))
      (_ , AlgebraEff UnitTy ([F] BoolTy))
    rawRec = recFA (_ , AlgebraEff UnitTy ([F] BoolTy))
      (λ V → seqS V [ret]')

    realizeTree : ∀ {t}
      → |FreeAlgebraᴰ| (λ V → ⟨ LogicalRelation BoolTy V ⟩) t
      → fiber interpretFreeBool (rawRec .fst t)
    realizeTree (|FreeAlgebraᴰ|.var {x = V} Vᴰ) .fst =
      |FreeAlgebra|.var (canonicalBool V Vᴰ .fst)
    realizeTree (|FreeAlgebraᴰ|.var {x = V} Vᴰ) .snd =
      cong₂ seqS
        (sym (canonicalBool V Vᴰ .snd))
        (sym [ret]'≡ret)
    realizeTree
      (|FreeAlgebraᴰ|.app op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩) .fst =
        |FreeAlgebra|.app op (λ v → realizeTree (γᴰ v) .fst)
    realizeTree
      (|FreeAlgebraᴰ|.app op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩) .snd =
        cong ([op] op) (funExt λ v → realizeTree (γᴰ v) .snd)
        ∙ rawRec .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩

    realizeRaw : ∀ {M} (raw : RawFBool M)
      → fiber interpretFreeBool M
    realizeRaw raw .fst = realizeTree (rawRelated raw) .fst
    realizeRaw raw .snd =
      realizeTree (rawRelated raw) .snd ∙ rawEquation raw

  closed-FBool-surjective : ∀ M → fiber interpretFreeBool M
  closed-FBool-surjective M = realizeRaw (raw-FBool M)

  unquote-FBool : Tm tt UnitTy ([F] BoolTy) → FreeAlgebra Bool .fst
  unquote-FBool M = closed-FBool-surjective M .fst

open BoolAlgebraSyntax public
