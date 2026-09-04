-- The algebraic theory of a read-only environment.
module Cubical.Algebra.Theory.Instances.Reader where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Theory.Base

private
  variable
    ℓR ℓV ℓX ℓB ℓD ℓD' : Level

data ReaderOp : Type ℓ-zero where
  ask : ReaderOp

ReaderSignature : (Env : Type ℓR) → Signature ℓ-zero ℓR
ReaderSignature Env .Signature.Op = ReaderOp
ReaderSignature Env .Signature.Arity ask = Env

module ReaderSignature {r : Level} (Env : Type r) where
  open Signature (ReaderSignature Env) public

module _ (Env : Type ℓR) where
  private
    module S = Signature (ReaderSignature Env)

  askTm : ∀ {V : Type ℓV}
    → (Env → S.|FreeAlgebra| V) → S.|FreeAlgebra| V
  askTm γ = S.app ask γ

  data ReaderEq : Type ℓ-zero where
    ask-constEq : ReaderEq
    ask-askEq : ReaderEq

  ReaderEqArity : ReaderEq → Type ℓR
  ReaderEqArity ask-constEq = Unit*
  ReaderEqArity ask-askEq = Env × Env

  ReaderLhs : (e : ReaderEq) → S.|FreeAlgebra| (ReaderEqArity e)
  ReaderLhs ask-constEq = askTm (λ _ → S.var tt*)
  ReaderLhs ask-askEq =
    askTm (λ r → askTm (λ r' → S.var (r , r')))

  ReaderRhs : (e : ReaderEq) → S.|FreeAlgebra| (ReaderEqArity e)
  ReaderRhs ask-constEq = S.var tt*
  ReaderRhs ask-askEq = askTm (λ r → S.var (r , r))

  ReaderTheory : Theory ℓ-zero ℓR ℓ-zero ℓR
  ReaderTheory .Theory.S = ReaderSignature Env
  ReaderTheory .Theory.Eq = ReaderEq
  ReaderTheory .Theory.EqArity = ReaderEqArity
  ReaderTheory .Theory.lhs = ReaderLhs
  ReaderTheory .Theory.rhs = ReaderRhs

module ReaderTheory {r : Level} (Env : Type r) where
  open Theory (ReaderTheory Env) public

module _ (Env : Type ℓR) (X : hSet ℓX) where
  private
    module T = Theory (ReaderTheory Env)

  ReaderFreeModel : T.Model (ℓ-max ℓR ℓX)
  ReaderFreeModel .fst .fst = Env → X .fst
  ReaderFreeModel .fst .snd ask γ r = γ r r
  ReaderFreeModel .snd .fst ask-constEq ρ =
    funExt λ _ → refl
  ReaderFreeModel .snd .fst ask-askEq ρ =
    funExt λ _ → refl
  ReaderFreeModel .snd .snd = isSetΠ λ _ → X .snd

  ReaderFreeModelη : X .fst → ReaderFreeModel .fst .fst
  ReaderFreeModelη x _ = x

  module _ (B : T.Model ℓB) (f : X .fst → B .fst .fst) where
    ReaderFreeModelRec : T.Homo (ReaderFreeModel .fst) (B .fst)
    ReaderFreeModelRec .fst g =
      B .fst .snd ask (λ r → f (g r))
    ReaderFreeModelRec .snd ask γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      B .snd .fst ask-askEq
        (λ { (r , r') → f (γ r r') })
      ∙ cong (ReaderFreeModelRec .fst) op∘γ≡op⟨γ⟩

    ReaderFreeModelRec-β : (x : X .fst) →
      ReaderFreeModelRec .fst (ReaderFreeModelη x) ≡ f x
    ReaderFreeModelRec-β x =
      B .snd .fst ask-constEq (λ _ → f x)

  ReaderFreeModelRec-uniq :
    (B : T.Model ℓB)
    (f : T.Homo (ReaderFreeModel .fst) (B .fst))
    → f .fst ≡
      ReaderFreeModelRec B (λ x → f .fst (ReaderFreeModelη x)) .fst
  ReaderFreeModelRec-uniq B f = funExt λ g →
    sym
      (f .snd ask (λ r → ReaderFreeModelη (g r)) g refl)

  ReaderFreeModelUniversal : (B : T.Model ℓB) →
    isEquiv
      (λ (f : T.Homo (ReaderFreeModel .fst) (B .fst)) x →
        f .fst (ReaderFreeModelη x))
  ReaderFreeModelUniversal B = isIsoToIsEquiv
    ( ReaderFreeModelRec B
    , (λ f → funExt (ReaderFreeModelRec-β B f))
    , (λ f → Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → B .snd .snd _ _)
        (sym (ReaderFreeModelRec-uniq B f)))
    )

  module _ (Xᴰ : X .fst → hSet ℓD) where
    private
      module R = hSetReasoning
        (ReaderFreeModel .fst .fst , ReaderFreeModel .snd .snd)
        (λ g → (r : Env) → Xᴰ (g r) .fst)

    ReaderFreeAlgebraᴰ :
      T.Algebraᴰ (ReaderFreeModel .fst) (ℓ-max ℓR ℓD)
    ReaderFreeAlgebraᴰ .fst g =
      (r : Env) → Xᴰ (g r) .fst
    ReaderFreeAlgebraᴰ .snd ask γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      R.reind op∘γ≡op⟨γ⟩ (λ r → γᴰ r r)

    ReaderOpNormalize :
      (γ : Env → ReaderFreeModel .fst .fst)
      (γᴰ : (r : Env) → ReaderFreeAlgebraᴰ .fst (γ r))
      → Path (T.∫Algebra ReaderFreeAlgebraᴰ .fst)
          ( ReaderFreeModel .fst .snd ask γ
          , ReaderFreeAlgebraᴰ .snd ask γ γᴰ _ refl)
          ( ReaderFreeModel .fst .snd ask γ
          , λ r → γᴰ r r)
    ReaderOpNormalize γ γᴰ = R.reind-filler⁻ refl

    ReaderAppFiller : {V : Type ℓV}
      ( ρ : V → ReaderFreeModel .fst .fst)
      (ρᴰ : (v : V) → ReaderFreeAlgebraᴰ .fst (ρ v))
      (γ : Env → T.|FreeAlgebra| V)
      → Path (T.∫Algebra ReaderFreeAlgebraᴰ .fst)
          ( ReaderFreeModel .fst .snd ask
              (λ r → T.interp (ReaderFreeModel .fst) ρ (γ r))
          , ReaderFreeAlgebraᴰ .snd ask
              (λ r → T.interp (ReaderFreeModel .fst) ρ (γ r))
              (λ r → T.interpᴰ ReaderFreeAlgebraᴰ ρ ρᴰ (γ r))
              _ refl)
          ( T.interp (ReaderFreeModel .fst) ρ (T.S.app ask γ)
          , T.interpᴰ ReaderFreeAlgebraᴰ ρ ρᴰ (T.S.app ask γ))
    ReaderAppFiller ρ ρᴰ γ =
      T.Algebraᴰ-op-filler ReaderFreeAlgebraᴰ ask
        (λ r → T.interp (ReaderFreeModel .fst) ρ (γ r))
        (λ r → T.interpᴰ ReaderFreeAlgebraᴰ ρ ρᴰ (γ r))
        (T.interp (ReaderFreeModel .fst) ρ (T.S.app ask γ))
        (T.recFA (ReaderFreeModel .fst) ρ .snd ask γ
          (T.S.app ask γ) refl)

    ReaderFreeModelᴰ :
      T.Modelᴰ ReaderFreeModel (ℓ-max ℓR ℓD)
    ReaderFreeModelᴰ .fst = ReaderFreeAlgebraᴰ
    ReaderFreeModelᴰ .snd .fst ask-constEq ρ ρᴰ =
      R.rectifyOut
        ( sym (ReaderAppFiller ρ ρᴰ (λ _ → T.S.var tt*))
        ∙ ReaderOpNormalize (λ _ → ρ tt*) (λ _ → ρᴰ tt*)
        ∙ etaPath)
      where
      etaPath : Path (T.∫Algebra ReaderFreeAlgebraᴰ .fst)
        ( ReaderFreeModel .fst .snd ask (λ _ → ρ tt*)
        , λ r → ρᴰ tt* r)
        (ρ tt* , ρᴰ tt*)
      etaPath i .fst r = ρ tt* r
      etaPath i .snd r = ρᴰ tt* r
    ReaderFreeModelᴰ .snd .fst ask-askEq ρ ρᴰ =
      R.rectifyOut
        ( sym (ReaderAppFiller ρ ρᴰ
            (λ r → T.S.app ask (λ r' → T.S.var (r , r'))))
        ∙ ReaderOpNormalize
            (λ r → T.interp (ReaderFreeModel .fst) ρ
              (T.S.app ask (λ r' → T.S.var (r , r'))))
            (λ r → T.interpᴰ ReaderFreeAlgebraᴰ ρ ρᴰ
              (T.S.app ask (λ r' → T.S.var (r , r'))))
        ∙ middlePath
        ∙ sym (ReaderOpNormalize
            (λ r → ρ (r , r)) (λ r → ρᴰ (r , r)))
        ∙ ReaderAppFiller ρ ρᴰ (λ r → T.S.var (r , r)))
      where
      innerPath : (r : Env) →
        Path (T.∫Algebra ReaderFreeAlgebraᴰ .fst)
          ( T.interp (ReaderFreeModel .fst) ρ
              (T.S.app ask (λ r' → T.S.var (r , r')))
          , T.interpᴰ ReaderFreeAlgebraᴰ ρ ρᴰ
              (T.S.app ask (λ r' → T.S.var (r , r'))))
          ( ReaderFreeModel .fst .snd ask (λ r' → ρ (r , r'))
          , λ r' → ρᴰ (r , r') r')
      innerPath r =
        sym (ReaderAppFiller ρ ρᴰ (λ r' → T.S.var (r , r')))
        ∙ ReaderOpNormalize (λ r' → ρ (r , r'))
            (λ r' → ρᴰ (r , r'))

      middlePath : Path (T.∫Algebra ReaderFreeAlgebraᴰ .fst)
        ( ReaderFreeModel .fst .snd ask
            (λ r → T.interp (ReaderFreeModel .fst) ρ
              (T.S.app ask (λ r' → T.S.var (r , r'))))
        , λ r → T.interpᴰ ReaderFreeAlgebraᴰ ρ ρᴰ
            (T.S.app ask (λ r' → T.S.var (r , r'))) r)
        ( ReaderFreeModel .fst .snd ask (λ r → ρ (r , r))
        , λ r → ρᴰ (r , r) r)
      middlePath i .fst r = innerPath r i .fst r
      middlePath i .snd r = innerPath r i .snd r
    ReaderFreeModelᴰ .snd .snd g =
      isSetΠ λ r → Xᴰ (g r) .snd

    ReaderFreeModelηᴰ : (x : X .fst) → Xᴰ x .fst →
      ReaderFreeModelᴰ .fst .fst (ReaderFreeModelη x)
    ReaderFreeModelηᴰ x xᴰ _ = xᴰ

    module _
      (Bᴰ : T.Modelᴰ ReaderFreeModel ℓD')
      (fᴰ : (x : X .fst) → Xᴰ x .fst →
        Bᴰ .fst .fst (ReaderFreeModelη x))
      where
      private
        module BᴰR = hSetReasoning
          (ReaderFreeModel .fst .fst , ReaderFreeModel .snd .snd)
          (Bᴰ .fst .fst)

      ReaderFreeModelRecᴰ-fun :
        (g : ReaderFreeModel .fst .fst) →
        ReaderFreeAlgebraᴰ .fst g → Bᴰ .fst .fst g
      ReaderFreeModelRecᴰ-fun g gᴰ =
        Bᴰ .fst .snd ask
          (λ r → ReaderFreeModelη (g r))
          (λ r → fᴰ (g r) (gᴰ r))
          g refl

      TargetAppFiller : {V : Type ℓV}
        ( ρ : V → ReaderFreeModel .fst .fst)
        (ρᴰ : (v : V) → Bᴰ .fst .fst (ρ v))
        (γ : Env → T.|FreeAlgebra| V)
        → Path (T.∫Algebra (Bᴰ .fst) .fst)
            ( ReaderFreeModel .fst .snd ask
                (λ r → T.interp (ReaderFreeModel .fst) ρ (γ r))
            , Bᴰ .fst .snd ask
                (λ r → T.interp (ReaderFreeModel .fst) ρ (γ r))
                (λ r → T.interpᴰ (Bᴰ .fst) ρ ρᴰ (γ r))
                _ refl)
            ( T.interp (ReaderFreeModel .fst) ρ (T.S.app ask γ)
            , T.interpᴰ (Bᴰ .fst) ρ ρᴰ (T.S.app ask γ))
      TargetAppFiller ρ ρᴰ γ =
        T.Algebraᴰ-op-filler (Bᴰ .fst) ask
          (λ r → T.interp (ReaderFreeModel .fst) ρ (γ r))
          (λ r → T.interpᴰ (Bᴰ .fst) ρ ρᴰ (γ r))
          (T.interp (ReaderFreeModel .fst) ρ (T.S.app ask γ))
          (T.recFA (ReaderFreeModel .fst) ρ .snd ask γ
            (T.S.app ask γ) refl)

      ReaderFreeModelRecᴰ-β : (x : X .fst) (xᴰ : Xᴰ x .fst) →
        ReaderFreeModelRecᴰ-fun
          (ReaderFreeModelη x) (ReaderFreeModelηᴰ x xᴰ) ≡ fᴰ x xᴰ
      ReaderFreeModelRecᴰ-β x xᴰ = BᴰR.rectifyOut {e' = refl}
        ( TargetAppFiller
            (λ (_ : Unit* {ℓR}) → ReaderFreeModelη x)
            (λ (_ : Unit* {ℓR}) → fᴰ x xᴰ)
            (λ (_ : Env) → T.S.var tt*)
        ∙ ΣPathP
            ( ReaderFreeModel .snd .fst ask-constEq
                (λ _ → ReaderFreeModelη x)
            , Bᴰ .snd .fst ask-constEq
                (λ _ → ReaderFreeModelη x) (λ _ → fᴰ x xᴰ)))

      private
        RecᴰTotal : T.∫Algebra ReaderFreeAlgebraᴰ .fst →
          T.∫Algebra (Bᴰ .fst) .fst
        RecᴰTotal z = z .fst , ReaderFreeModelRecᴰ-fun (z .fst) (z .snd)

      ReaderFreeModelRecᴰ :
        T.Homoᴰ (T.idHomo {A = ReaderFreeModel .fst})
          ReaderFreeAlgebraᴰ (Bᴰ .fst)
      ReaderFreeModelRecᴰ .fst = ReaderFreeModelRecᴰ-fun
      ReaderFreeModelRecᴰ .snd ask γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
        op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
          BᴰR.rectifyOut {e' = refl}
            ( sym (T.Algebraᴰ-op-filler (Bᴰ .fst) ask γ
                (λ r → ReaderFreeModelRecᴰ-fun (γ r) (γᴰ r))
                op⟨γ⟩ op∘γ≡op⟨γ⟩)
            ∙ cong (T.∫Algebra (Bᴰ .fst) .snd ask)
                (funExt λ r → TargetAppFiller valuation valuationᴰ
                  (λ r' → T.S.var (r , r')))
            ∙ TargetAppFiller valuation valuationᴰ
                (λ r → T.S.app ask (λ r' → T.S.var (r , r')))
            ∙ ΣPathP
                ( ReaderFreeModel .snd .fst ask-askEq valuation
                , Bᴰ .snd .fst ask-askEq valuation valuationᴰ)
            ∙ sym (TargetAppFiller valuation valuationᴰ
                (λ r → T.S.var (r , r)))
            ∙ cong RecᴰTotal sourcePath)
          where
          valuation : Env × Env → ReaderFreeModel .fst .fst
          valuation (r , r') = ReaderFreeModelη (γ r r')

          valuationᴰ : (rr' : Env × Env) →
            Bᴰ .fst .fst (valuation rr')
          valuationᴰ (r , r') = fᴰ (γ r r') (γᴰ r r')

          sourcePath : Path (T.∫Algebra ReaderFreeAlgebraᴰ .fst)
            (ReaderFreeModel .fst .snd ask γ , λ r → γᴰ r r)
            (op⟨γ⟩ , op⟨γᴰ⟩)
          sourcePath =
            R.reind-filler op∘γ≡op⟨γ⟩ ∙ R.≡in op∘γᴰ≡op⟨γᴰ⟩

    ReaderFreeModelRecᴰ-uniq :
      (Bᴰ : T.Modelᴰ ReaderFreeModel ℓD')
      (hᴰ : T.Homoᴰ (T.idHomo {A = ReaderFreeModel .fst})
        ReaderFreeAlgebraᴰ (Bᴰ .fst))
      → hᴰ .fst ≡
        ReaderFreeModelRecᴰ Bᴰ
          (λ x xᴰ → hᴰ .fst
            (ReaderFreeModelη x) (ReaderFreeModelηᴰ x xᴰ)) .fst
    ReaderFreeModelRecᴰ-uniq Bᴰ hᴰ =
      funExt λ g → funExt λ gᴰ →
        sym
          (hᴰ .snd ask
            (λ r → ReaderFreeModelη (g r))
            (λ r → ReaderFreeModelηᴰ (g r) (gᴰ r))
            g refl gᴰ (sourceᴰ≡ g gᴰ))
      where
      sourceᴰ≡ : (g : ReaderFreeModel .fst .fst)
        (gᴰ : ReaderFreeAlgebraᴰ .fst g) →
        ReaderFreeAlgebraᴰ .snd ask
          (λ r → ReaderFreeModelη (g r))
          (λ r → ReaderFreeModelηᴰ (g r) (gᴰ r))
          g refl
        ≡ gᴰ
      sourceᴰ≡ g gᴰ = R.rectifyOut {e' = refl} (R.reind-filler⁻ refl)

    ReaderFreeModelUniversalᴰ :
      (Bᴰ : T.Modelᴰ ReaderFreeModel ℓD') →
      isEquiv
        (λ (hᴰ : T.Homoᴰ (T.idHomo {A = ReaderFreeModel .fst})
            ReaderFreeAlgebraᴰ (Bᴰ .fst)) x xᴰ →
          hᴰ .fst (ReaderFreeModelη x) (ReaderFreeModelηᴰ x xᴰ))
    ReaderFreeModelUniversalᴰ Bᴰ = isIsoToIsEquiv
      ( ReaderFreeModelRecᴰ Bᴰ
      , (λ fᴰ → funExt λ x → funExt λ xᴰ →
          ReaderFreeModelRecᴰ-β Bᴰ fᴰ x xᴰ)
      , (λ hᴰ → Σ≡Prop
          (λ _ → isPropΠ6 λ _ _ _ _ _ _ →
            isPropΠ λ _ → Bᴰ .snd .snd _ _ _)
          (sym (ReaderFreeModelRecᴰ-uniq Bᴰ hᴰ)))
      )

    module _ {B : T.Model ℓB}
      (ϕ : T.Homo (ReaderFreeModel .fst) (B .fst))
      (Bᴰ : T.Modelᴰ B ℓD')
      (fᴰ : (x : X .fst) → Xᴰ x .fst →
        Bᴰ .fst .fst (ϕ .fst (ReaderFreeModelη x)))
      where
      ReaderFreeModelRecOverᴰ :
        T.Homoᴰ ϕ ReaderFreeAlgebraᴰ (Bᴰ .fst)
      ReaderFreeModelRecOverᴰ =
        ReaderFreeModelRecᴰ
          (T._*_ {M = ReaderFreeModel} {N = B} ϕ Bᴰ) fᴰ

      ReaderFreeModelRecOverᴰ-β :
        (x : X .fst) (xᴰ : Xᴰ x .fst) →
        ReaderFreeModelRecOverᴰ .fst
          (ReaderFreeModelη x) (ReaderFreeModelηᴰ x xᴰ) ≡ fᴰ x xᴰ
      ReaderFreeModelRecOverᴰ-β =
        ReaderFreeModelRecᴰ-β
          (T._*_ {M = ReaderFreeModel} {N = B} ϕ Bᴰ) fᴰ

    ReaderFreeModelRecOverᴰ-uniq : {B : T.Model ℓB}
      (ϕ : T.Homo (ReaderFreeModel .fst) (B .fst))
      (Bᴰ : T.Modelᴰ B ℓD')
      (hᴰ : T.Homoᴰ ϕ ReaderFreeAlgebraᴰ (Bᴰ .fst))
      → hᴰ .fst ≡ ReaderFreeModelRecOverᴰ {B = B} ϕ Bᴰ
          (λ x xᴰ → hᴰ .fst
            (ReaderFreeModelη x) (ReaderFreeModelηᴰ x xᴰ)) .fst
    ReaderFreeModelRecOverᴰ-uniq {B = B} ϕ Bᴰ =
      ReaderFreeModelRecᴰ-uniq
        (T._*_ {M = ReaderFreeModel} {N = B} ϕ Bᴰ)

    ReaderFreeModelUniversalOverᴰ : {B : T.Model ℓB}
      (ϕ : T.Homo (ReaderFreeModel .fst) (B .fst))
      (Bᴰ : T.Modelᴰ B ℓD') →
      isEquiv
        (λ (hᴰ : T.Homoᴰ ϕ ReaderFreeAlgebraᴰ (Bᴰ .fst)) x xᴰ →
          hᴰ .fst (ReaderFreeModelη x) (ReaderFreeModelηᴰ x xᴰ))
    ReaderFreeModelUniversalOverᴰ {B = B} ϕ Bᴰ =
      ReaderFreeModelUniversalᴰ
        (T._*_ {M = ReaderFreeModel} {N = B} ϕ Bᴰ)
