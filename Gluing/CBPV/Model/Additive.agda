{-# OPTIONS --prop --lossy-unification #-}
module Gluing.CBPV.Model.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure

open import Cubical.Prop

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

open import Cubical.Algebra.Theory.Base
  hiding (ℓ; ℓᴰ; ℓᴰᴰ; ℓ'; ℓᴰ'; ℓᴰᴰ'; ℓ''; ℓᴰ''; ℓO; ℓA; ℓE)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞;
    ≤Vertex to ≤Kind)
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
  renaming (Section to DisplayedSection)
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Model
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Multiplicative
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Additive
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.ModelEnriched.Additive
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Instances.Algebra.DisplayedModel

open Category
open Functor
open Functorᴰ
open DisplayedSection

private
  variable
    ℓO ℓA ℓE ℓEA : Level

-- The logical-relations model is parameterized by the ordinary and displayed
-- free-model universal properties used to interpret F.
module ModelGluingWithFree
  (T : Theory ℓO ℓA ℓE ℓEA)
  (Free : FreeMODELConstruction T)
  (BaseTy : Kind → Type (ModelLevel T))
  (Fun : ∀ {k₁ k₂} → ≤Kind k₁ k₂
    → CBPV.Ob T BaseTy k₁ → CBPV.Ob T BaseTy k₂
    → Type (ModelLevel T))
  (I : CBPV.Ob T BaseTy 𝒱)
  where
  open CBPV T BaseTy
  open Terms Fun

  pts : Functorⱽ (AddCBPV .fst .fst)
    (ModelAddCBPVWithFree T (Free .fst) .fst .fst)
  pts = points T (AddCBPV .fst .fst) CBPVModel I

  ptsPreservesModel : PreservesModelEnrichment T pts
    CBPVModel (ModelCBPVModel T)
  ptsPreservesModel =
    pointsPreservesModel T (AddCBPV .fst .fst) CBPVModel I

-- The Boolean canonicity theorem additionally chooses the desired concrete
-- presentation of the free model on Bool.  It need not be the same datatype
-- used internally by the free adjunction above.
module BoolModelSyntaxWithFree
  (T : Theory ℓO ℓA ℓE ℓEA)
  (Free : FreeMODELConstruction T)
  (FreeBool : BoolFreeMODELConstruction T)
  where
  open Theory T

  private
    L = ModelLevel T

  data BaseTy (k : Kind) : Type L where

  open CBPV T BaseTy

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

  module G = ModelGluingWithFree T Free BaseTy FUN UnitTy

  module Fundamental = LocalElim
    G.pts
    (ModelAddCBPVⱽWithFree T Free)
    (ModelCBPVModel T)
    G.ptsPreservesModel
    (ModelCBPVModelᴰ T)

  baseObject : ∀ {k} (X : BaseTy k)
    → Categoryᴰ.ob[_] (ModelAddCBPVⱽWithFree T Free .fst .fst)
        (k , G.pts .F-obᴰ (gen X))
  baseObject ()

  fundamentalLemma :
    DisplayedSection (∫F G.pts)
      (ModelAddCBPVⱽWithFree T Free .fst .fst)
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

  private
    SyntaxModel : Model L
    SyntaxModel =
      ModelEnrichmentModel CBPV T CBPVModel UnitTy ([F] BoolTy)

    SyntaxMODEL : Category.ob (MODEL T L)
    SyntaxMODEL .fst = SyntaxModel .fst .fst , SyntaxModel .snd .snd
    SyntaxMODEL .snd .fst = SyntaxModel .fst .snd
    SyntaxMODEL .snd .snd = SyntaxModel .snd .fst

    SyntaxBoolSET : hSet L
    SyntaxBoolSET = G.pts .F-obᴰ BoolTy

    SyntaxBoolRelation : ⟨ SyntaxBoolSET ⟩ → hSet L
    SyntaxBoolRelation = LogicalRelation BoolTy

    RawFreeMODEL : Category.ob (MODEL T L)
    RawFreeMODEL = Free .fst SyntaxBoolSET .UniversalElement.vertex

    RawFreeLift : CartesianLift
      ((ModelCBPVᴰWithFree T (Free .fst)) ^opᴰᴰ)
      (FreeMODELη T (Free .fst) SyntaxBoolSET) SyntaxBoolRelation
    RawFreeLift = Free .snd SyntaxBoolSET SyntaxBoolRelation

    RawFreeMODELᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) RawFreeMODEL
    RawFreeMODELᴰ = RawFreeLift .fst

    rawRec : MODEL T L [ RawFreeMODEL , SyntaxMODEL ]
    rawRec = isEquivToIsIso _
      (Free .fst SyntaxBoolSET .UniversalElement.universal SyntaxMODEL)
      .fst (λ V → seqS V [ret]')

    rawβ :
      (λ V → rawRec .fst
        (Free .fst SyntaxBoolSET .UniversalElement.element V))
      ≡ (λ V → seqS V [ret]')
    rawβ = isEquivToIsIso _
      (Free .fst SyntaxBoolSET .UniversalElement.universal SyntaxMODEL)
      .snd .fst (λ V → seqS V [ret]')

    FreeBoolMODEL : Category.ob (MODEL T L)
    FreeBoolMODEL = FreeBool .fst

    ηBool : Bool → ⟨ FreeBoolMODEL .fst ⟩
    ηBool = FreeBool .snd .fst

    interpretFreeBoolHomo : MODEL T L [ FreeBoolMODEL , SyntaxMODEL ]
    interpretFreeBoolHomo = isEquivToIsIso _
      (FreeBool .snd .snd SyntaxMODEL) .fst
      (λ b → seqS (quoteBool b) [ret])

    interpretβ : (λ b → interpretFreeBoolHomo .fst (ηBool b))
      ≡ (λ b → seqS (quoteBool b) [ret])
    interpretβ = isEquivToIsIso _
      (FreeBool .snd .snd SyntaxMODEL) .snd .fst
      (λ b → seqS (quoteBool b) [ret])

  interpretFreeBool :
    ⟨ FreeBoolMODEL .fst ⟩ → Tm tt UnitTy ([F] BoolTy)
  interpretFreeBool = interpretFreeBoolHomo .fst

  private
    rawTerm : ∀ {M} → RawFBool M
      → ⟨ RawFreeMODEL .fst ⟩
    rawTerm raw = raw .fst

    rawRelated : ∀ {M} (raw : RawFBool M)
      → ⟨ RawFreeMODELᴰ .fst (rawTerm raw) ⟩
    rawRelated raw = raw .snd .snd

    rawEquation : ∀ {M} (raw : RawFBool M)
      → rawRec .fst (rawTerm raw) ≡ M
    rawEquation raw = raw .snd .fst

    UnitFreeBoolMODELᴰ :
      Categoryᴰ.ob[_] (MODELᴰ T L L) FreeBoolMODEL
    UnitFreeBoolMODELᴰ = TerminalsⱽMODELᴰ T FreeBoolMODEL .fst

    RealizerMODELᴰ : Categoryᴰ.ob[_] (MODELᴰ T L L) SyntaxMODEL
    RealizerMODELᴰ =
      PushMODELᴰ T interpretFreeBoolHomo UnitFreeBoolMODELᴰ

    RealizerModelᴰ : Modelᴰ SyntaxModel L
    RealizerModelᴰ .fst .fst M = ⟨ RealizerMODELᴰ .fst M ⟩
    RealizerModelᴰ .fst .snd = RealizerMODELᴰ .snd .fst
    RealizerModelᴰ .snd .fst = RealizerMODELᴰ .snd .snd
    RealizerModelᴰ .snd .snd M = RealizerMODELᴰ .fst M .snd

    realizeVar : ∀ V → ⟨ LogicalRelation BoolTy V ⟩
      → RealizerModelᴰ .fst .fst
          (rawRec .fst
            (Free .fst SyntaxBoolSET .UniversalElement.element V))
    realizeVar V Vᴰ .fst =
      ηBool (canonicalBool V Vᴰ .fst)
    realizeVar V Vᴰ .snd .fst =
      funExt⁻ interpretβ (canonicalBool V Vᴰ .fst)
      ∙ cong₂ seqS
          (sym (canonicalBool V Vᴰ .snd))
          (sym [ret]'≡ret)
      ∙ sym (funExt⁻ rawβ V)
    realizeVar V Vᴰ .snd .snd = tt*

    module ModelCop = Category
      (∫C (ModelCBPVWithFree T (Free .fst) .fst ^opᴰ))

    rawRecᵒᵖ : ∫C (ModelCBPVWithFree T (Free .fst) .fst ^opᴰ)
      [ (Kind.r , SyntaxMODEL) , (Kind.r , RawFreeMODEL) ]
    rawRecᵒᵖ = _ , rawRec

    rawFactor : ∫C (ModelCBPVWithFree T (Free .fst) .fst ^opᴰ)
      [ (Kind.r , SyntaxMODEL) , (Kind.l , SyntaxBoolSET) ]
    rawFactor = rawRecᵒᵖ ModelCop.⋆
      FreeMODELη T (Free .fst) SyntaxBoolSET

    realizeGenerator : Categoryᴰ.Hom[_][_,_]
      ((ModelCBPVᴰWithFree T (Free .fst)) ^opᴰᴰ)
      rawFactor RealizerMODELᴰ SyntaxBoolRelation
    realizeGenerator = realizeVar

    -- Use the displayed free-model universal property to extend the
    -- generator realization.  This is the only recursion over the chosen
    -- free displayed model, so the proof never inspects its constructors.
    realizeFreeᴰᵒᵖ : Categoryᴰ.Hom[_][_,_]
      ((ModelCBPVᴰWithFree T (Free .fst)) ^opᴰᴰ)
      rawRecᵒᵖ RealizerMODELᴰ RawFreeMODELᴰ
    realizeFreeᴰᵒᵖ =
      CartesianLiftNotation.introᴰ
        ((ModelCBPVᴰWithFree T (Free .fst)) ^opᴰᴰ)
        RawFreeLift
        {Γ = (Kind.r , SyntaxMODEL)}
        {Γᴰ = RealizerMODELᴰ}
        {g = rawRecᵒᵖ}
        realizeGenerator

    realizeTreeᴰ : ∀ {t} → ⟨ RawFreeMODELᴰ .fst t ⟩
      → RealizerModelᴰ .fst .fst (rawRec .fst t)
    realizeTreeᴰ {t = t} tᴰ = realizeFreeᴰᵒᵖ .fst t tᴰ

    realizeTree : ∀ {t}
      → ⟨ RawFreeMODELᴰ .fst t ⟩
      → fiber interpretFreeBool (rawRec .fst t)
    realizeTree tᴰ .fst = realizeTreeᴰ tᴰ .fst
    realizeTree tᴰ .snd = realizeTreeᴰ tᴰ .snd .fst

    realizeRaw : ∀ {M} (raw : RawFBool M)
      → fiber interpretFreeBool M
    realizeRaw raw .fst = realizeTree (rawRelated raw) .fst
    realizeRaw raw .snd =
      realizeTree (rawRelated raw) .snd ∙ rawEquation raw

  closed-FBool-surjective : ∀ M → fiber interpretFreeBool M
  closed-FBool-surjective M = realizeRaw (raw-FBool M)

  unquote-FBool : Tm tt UnitTy ([F] BoolTy)
    → ⟨ FreeBool .fst .fst ⟩
  unquote-FBool M = closed-FBool-surjective M .fst

module ModelGluing
  {ℓO ℓA ℓE ℓEA : Level}
  (T : Theory ℓO ℓA ℓE ℓEA)
  (BaseTy : Kind → Type (ModelLevel T))
  (Fun : ∀ {k₁ k₂} → ≤Kind k₁ k₂
    → CBPV.Ob T BaseTy k₁ → CBPV.Ob T BaseTy k₂
    → Type (ModelLevel T))
  (I : CBPV.Ob T BaseTy Kind.l) =
  ModelGluingWithFree T (CanonicalFreeMODELConstruction T)
    BaseTy Fun I

module BoolModelSyntax
  {ℓO ℓA ℓE ℓEA : Level}
  (T : Theory ℓO ℓA ℓE ℓEA) =
  BoolModelSyntaxWithFree T
    (CanonicalFreeMODELConstruction T)
    (CanonicalBoolFreeMODELConstruction T)

open BoolModelSyntax public
