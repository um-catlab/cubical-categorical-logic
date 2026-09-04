-- The algebraic theory of a monoidal write-only output.
module Cubical.Algebra.Theory.Instances.Writer where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Theory.Base

private
  variable
    ℓW ℓV ℓX ℓB ℓD ℓD' : Level

data WriterOp {w : Level} (Output : Type w) : Type w where
  tell : Output → WriterOp Output

WriterSignature : (Output : Type ℓW) → Signature ℓW ℓ-zero
WriterSignature Output .Signature.Op = WriterOp Output
WriterSignature Output .Signature.Arity (tell _) = Unit

module WriterSignature {w : Level} (Output : Type w) where
  open Signature (WriterSignature Output) public

module _ (Output : Type ℓW) where
  private
    module S = Signature (WriterSignature Output)

  tellTm : ∀ {V : Type ℓV}
    → Output → S.|FreeAlgebra| V → S.|FreeAlgebra| V
  tellTm w t = S.app (tell w) (λ _ → t)

  data WriterEq : Type ℓW where
    tell-idEq : WriterEq
    tell-tellEq : Output → Output → WriterEq

  WriterEqArity : WriterEq → Type ℓ-zero
  WriterEqArity tell-idEq = Unit
  WriterEqArity (tell-tellEq _ _) = Unit

module _ (W : Monoid ℓW) where
  private
    module W = MonoidStr (W .snd)
    module S = Signature (WriterSignature (W .fst))

  WriterLhs : (e : WriterEq (W .fst))
    → S.|FreeAlgebra| (WriterEqArity (W .fst) e)
  WriterLhs tell-idEq = tellTm (W .fst) W.ε (S.var tt)
  WriterLhs (tell-tellEq w w') =
    tellTm (W .fst) w (tellTm (W .fst) w' (S.var tt))

  WriterRhs : (e : WriterEq (W .fst))
    → S.|FreeAlgebra| (WriterEqArity (W .fst) e)
  WriterRhs tell-idEq = S.var tt
  WriterRhs (tell-tellEq w w') =
    tellTm (W .fst) (W._·_ w w') (S.var tt)

  WriterTheory : Theory ℓW ℓ-zero ℓW ℓ-zero
  WriterTheory .Theory.S = WriterSignature (W .fst)
  WriterTheory .Theory.Eq = WriterEq (W .fst)
  WriterTheory .Theory.EqArity = WriterEqArity (W .fst)
  WriterTheory .Theory.lhs = WriterLhs
  WriterTheory .Theory.rhs = WriterRhs

module WriterTheory {w : Level} (W : Monoid w) where
  open Theory (WriterTheory W) public

module _ (W : Monoid ℓW) (X : hSet ℓX) where
  private
    module W = MonoidStr (W .snd)
    module T = Theory (WriterTheory W)

  WriterFreeModel : T.Model (ℓ-max ℓW ℓX)
  WriterFreeModel .fst .fst = W .fst × X .fst
  WriterFreeModel .fst .snd (tell w) γ =
    W._·_ w (γ tt .fst) , γ tt .snd
  WriterFreeModel .snd .fst tell-idEq ρ =
    ΣPathP (W.·IdL (ρ tt .fst) , refl)
  WriterFreeModel .snd .fst (tell-tellEq w w') ρ =
    ΣPathP (W.·Assoc w w' (ρ tt .fst) , refl)
  WriterFreeModel .snd .snd = isSet× W.is-set (X .snd)

  WriterFreeModelη : X .fst → WriterFreeModel .fst .fst
  WriterFreeModelη x = W.ε , x

  module _ (B : T.Model ℓB) (f : X .fst → B .fst .fst) where
    WriterFreeModelRec : T.Homo (WriterFreeModel .fst) (B .fst)
    WriterFreeModelRec .fst (w , x) =
      B .fst .snd (tell w) (λ _ → f x)
    WriterFreeModelRec .snd (tell w) γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      B .snd .fst (tell-tellEq w (γ tt .fst))
        (λ _ → f (γ tt .snd))
      ∙ cong (WriterFreeModelRec .fst) op∘γ≡op⟨γ⟩

    WriterFreeModelRec-β : (x : X .fst) →
      WriterFreeModelRec .fst (WriterFreeModelη x) ≡ f x
    WriterFreeModelRec-β x =
      B .snd .fst tell-idEq (λ _ → f x)

  WriterFreeModelRec-uniq :
    (B : T.Model ℓB)
    (f : T.Homo (WriterFreeModel .fst) (B .fst))
    → f .fst ≡
      WriterFreeModelRec B (λ x → f .fst (WriterFreeModelη x)) .fst
  WriterFreeModelRec-uniq B f = funExt λ { (w , x) →
    sym
      (f .snd (tell w) (λ _ → WriterFreeModelη x) (w , x)
        (ΣPathP (W.·IdR w , refl))) }

  WriterFreeModelUniversal : (B : T.Model ℓB) →
    isEquiv
      (λ (f : T.Homo (WriterFreeModel .fst) (B .fst)) x →
        f .fst (WriterFreeModelη x))
  WriterFreeModelUniversal B = isIsoToIsEquiv
    ( WriterFreeModelRec B
    , (λ f → funExt (WriterFreeModelRec-β B f))
    , (λ f → Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → B .snd .snd _ _)
        (sym (WriterFreeModelRec-uniq B f)))
    )

  module _ (Xᴰ : X .fst → hSet ℓD) where
    private
      module R = hSetReasoning
        (WriterFreeModel .fst .fst , WriterFreeModel .snd .snd)
        (λ wx → Xᴰ (wx .snd) .fst)

    WriterFreeAlgebraᴰ :
      T.Algebraᴰ (WriterFreeModel .fst) ℓD
    WriterFreeAlgebraᴰ .fst wx = Xᴰ (wx .snd) .fst
    WriterFreeAlgebraᴰ .snd (tell w) γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      R.reind op∘γ≡op⟨γ⟩ (γᴰ tt)

    WriterOpNormalize :
      (w : W .fst)
      (γ : Unit → WriterFreeModel .fst .fst)
      (γᴰ : (u : Unit) → WriterFreeAlgebraᴰ .fst (γ u))
      → Path (T.∫Algebra WriterFreeAlgebraᴰ .fst)
          ( WriterFreeModel .fst .snd (tell w) γ
          , WriterFreeAlgebraᴰ .snd (tell w) γ γᴰ _ refl)
          ( WriterFreeModel .fst .snd (tell w) γ
          , γᴰ tt)
    WriterOpNormalize w γ γᴰ = R.reind-filler⁻ refl

    WriterAppFiller : {V : Type ℓV}
      (w : W .fst)
      (ρ : V → WriterFreeModel .fst .fst)
      (ρᴰ : (v : V) → WriterFreeAlgebraᴰ .fst (ρ v))
      (γ : Unit → T.|FreeAlgebra| V)
      → Path (T.∫Algebra WriterFreeAlgebraᴰ .fst)
          ( WriterFreeModel .fst .snd (tell w)
              (λ u → T.interp (WriterFreeModel .fst) ρ (γ u))
          , WriterFreeAlgebraᴰ .snd (tell w)
              (λ u → T.interp (WriterFreeModel .fst) ρ (γ u))
              (λ u → T.interpᴰ WriterFreeAlgebraᴰ ρ ρᴰ (γ u))
              _ refl)
          ( T.interp (WriterFreeModel .fst) ρ (T.S.app (tell w) γ)
          , T.interpᴰ WriterFreeAlgebraᴰ ρ ρᴰ
              (T.S.app (tell w) γ))
    WriterAppFiller w ρ ρᴰ γ =
      T.Algebraᴰ-op-filler WriterFreeAlgebraᴰ (tell w)
        (λ u → T.interp (WriterFreeModel .fst) ρ (γ u))
        (λ u → T.interpᴰ WriterFreeAlgebraᴰ ρ ρᴰ (γ u))
        (T.interp (WriterFreeModel .fst) ρ (T.S.app (tell w) γ))
        (T.recFA (WriterFreeModel .fst) ρ .snd (tell w) γ
          (T.S.app (tell w) γ) refl)

    WriterFreeModelᴰ : T.Modelᴰ WriterFreeModel ℓD
    WriterFreeModelᴰ .fst = WriterFreeAlgebraᴰ
    WriterFreeModelᴰ .snd .fst tell-idEq ρ ρᴰ =
      R.rectifyOut
        {e' = WriterFreeModel .snd .fst tell-idEq ρ}
        ( sym (WriterAppFiller W.ε ρ ρᴰ (λ _ → T.S.var tt))
        ∙ WriterOpNormalize W.ε (λ _ → ρ tt) (λ _ → ρᴰ tt)
        ∙ unitPath)
      where
      unitPath : Path (T.∫Algebra WriterFreeAlgebraᴰ .fst)
        ( (W._·_ W.ε (ρ tt .fst) , ρ tt .snd) , ρᴰ tt)
        (ρ tt , ρᴰ tt)
      unitPath i .fst .fst = W.·IdL (ρ tt .fst) i
      unitPath i .fst .snd = ρ tt .snd
      unitPath i .snd = ρᴰ tt
    WriterFreeModelᴰ .snd .fst (tell-tellEq w w') ρ ρᴰ =
      R.rectifyOut
        {e' = WriterFreeModel .snd .fst (tell-tellEq w w') ρ}
        ( sym (WriterAppFiller w ρ ρᴰ
            (λ _ → T.S.app (tell w') (λ _ → T.S.var tt)))
        ∙ WriterOpNormalize w
            (λ _ → T.interp (WriterFreeModel .fst) ρ
              (T.S.app (tell w') (λ _ → T.S.var tt)))
            (λ _ → T.interpᴰ WriterFreeAlgebraᴰ ρ ρᴰ
              (T.S.app (tell w') (λ _ → T.S.var tt)))
        ∙ cong leftMultiplyTotal innerPath
        ∙ assocPath
        ∙ sym (WriterOpNormalize (W._·_ w w')
            (λ _ → ρ tt) (λ _ → ρᴰ tt))
        ∙ WriterAppFiller (W._·_ w w') ρ ρᴰ
            (λ _ → T.S.var tt))
      where
      innerPath : Path (T.∫Algebra WriterFreeAlgebraᴰ .fst)
        ( T.interp (WriterFreeModel .fst) ρ
            (T.S.app (tell w') (λ _ → T.S.var tt))
        , T.interpᴰ WriterFreeAlgebraᴰ ρ ρᴰ
            (T.S.app (tell w') (λ _ → T.S.var tt)))
        ( (W._·_ w' (ρ tt .fst) , ρ tt .snd) , ρᴰ tt)
      innerPath =
        sym (WriterAppFiller w' ρ ρᴰ (λ _ → T.S.var tt))
        ∙ WriterOpNormalize w' (λ _ → ρ tt) (λ _ → ρᴰ tt)

      leftMultiplyTotal : T.∫Algebra WriterFreeAlgebraᴰ .fst →
        T.∫Algebra WriterFreeAlgebraᴰ .fst
      leftMultiplyTotal z =
        (W._·_ w (z .fst .fst) , z .fst .snd) , z .snd

      assocPath : Path (T.∫Algebra WriterFreeAlgebraᴰ .fst)
        ( (W._·_ w (W._·_ w' (ρ tt .fst)) , ρ tt .snd) , ρᴰ tt)
        ( (W._·_ (W._·_ w w') (ρ tt .fst) , ρ tt .snd) , ρᴰ tt)
      assocPath i .fst .fst = W.·Assoc w w' (ρ tt .fst) i
      assocPath i .fst .snd = ρ tt .snd
      assocPath i .snd = ρᴰ tt
    WriterFreeModelᴰ .snd .snd wx = Xᴰ (wx .snd) .snd

    WriterFreeModelηᴰ : (x : X .fst) → Xᴰ x .fst →
      WriterFreeModelᴰ .fst .fst (WriterFreeModelη x)
    WriterFreeModelηᴰ x xᴰ = xᴰ

    module _
      (Bᴰ : T.Modelᴰ WriterFreeModel ℓD')
      (fᴰ : (x : X .fst) → Xᴰ x .fst →
        Bᴰ .fst .fst (WriterFreeModelη x))
      where
      private
        module BᴰR = hSetReasoning
          (WriterFreeModel .fst .fst , WriterFreeModel .snd .snd)
          (Bᴰ .fst .fst)

      WriterFreeModelRecᴰ-fun :
        (wx : WriterFreeModel .fst .fst) →
        WriterFreeAlgebraᴰ .fst wx → Bᴰ .fst .fst wx
      WriterFreeModelRecᴰ-fun (w , x) xᴰ =
        Bᴰ .fst .snd (tell w)
          (λ _ → WriterFreeModelη x)
          (λ _ → fᴰ x xᴰ)
          (w , x) (ΣPathP (W.·IdR w , refl))

      TargetAppFiller : {V : Type ℓV}
        (w : W .fst)
        (ρ : V → WriterFreeModel .fst .fst)
        (ρᴰ : (v : V) → Bᴰ .fst .fst (ρ v))
        (γ : Unit → T.|FreeAlgebra| V)
        → Path (T.∫Algebra (Bᴰ .fst) .fst)
            ( WriterFreeModel .fst .snd (tell w)
                (λ u → T.interp (WriterFreeModel .fst) ρ (γ u))
            , Bᴰ .fst .snd (tell w)
                (λ u → T.interp (WriterFreeModel .fst) ρ (γ u))
                (λ u → T.interpᴰ (Bᴰ .fst) ρ ρᴰ (γ u))
                _ refl)
            ( T.interp (WriterFreeModel .fst) ρ
                (T.S.app (tell w) γ)
            , T.interpᴰ (Bᴰ .fst) ρ ρᴰ (T.S.app (tell w) γ))
      TargetAppFiller w ρ ρᴰ γ =
        T.Algebraᴰ-op-filler (Bᴰ .fst) (tell w)
          (λ u → T.interp (WriterFreeModel .fst) ρ (γ u))
          (λ u → T.interpᴰ (Bᴰ .fst) ρ ρᴰ (γ u))
          (T.interp (WriterFreeModel .fst) ρ (T.S.app (tell w) γ))
          (T.recFA (WriterFreeModel .fst) ρ .snd (tell w) γ
            (T.S.app (tell w) γ) refl)

      WriterFreeModelRecᴰ-β : (x : X .fst) (xᴰ : Xᴰ x .fst) →
        WriterFreeModelRecᴰ-fun
          (WriterFreeModelη x) (WriterFreeModelηᴰ x xᴰ) ≡ fᴰ x xᴰ
      WriterFreeModelRecᴰ-β x xᴰ = BᴰR.rectifyOut {e' = refl}
        ( sym (T.Algebraᴰ-op-filler (Bᴰ .fst) (tell W.ε)
            (λ _ → WriterFreeModelη x) (λ _ → fᴰ x xᴰ)
            (WriterFreeModelη x) (ΣPathP (W.·IdR W.ε , refl)))
        ∙ TargetAppFiller W.ε
            (λ (_ : Unit) → WriterFreeModelη x)
            (λ (_ : Unit) → fᴰ x xᴰ)
            (λ _ → T.S.var tt)
        ∙ ΣPathP
            ( WriterFreeModel .snd .fst tell-idEq
                (λ _ → WriterFreeModelη x)
            , Bᴰ .snd .fst tell-idEq
                (λ _ → WriterFreeModelη x) (λ _ → fᴰ x xᴰ)))

      private
        RecᴰTotal : T.∫Algebra WriterFreeAlgebraᴰ .fst →
          T.∫Algebra (Bᴰ .fst) .fst
        RecᴰTotal z =
          z .fst , WriterFreeModelRecᴰ-fun (z .fst) (z .snd)

      WriterFreeModelRecᴰ :
        T.Homoᴰ (T.idHomo {A = WriterFreeModel .fst})
          WriterFreeAlgebraᴰ (Bᴰ .fst)
      WriterFreeModelRecᴰ .fst = WriterFreeModelRecᴰ-fun
      WriterFreeModelRecᴰ .snd (tell w) γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
        op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
          BᴰR.rectifyOut {e' = refl}
            ( sym (T.Algebraᴰ-op-filler (Bᴰ .fst) (tell w) γ
                (λ u → WriterFreeModelRecᴰ-fun (γ u) (γᴰ u))
                op⟨γ⟩ op∘γ≡op⟨γ⟩)
            ∙ cong (T.∫Algebra (Bᴰ .fst) .snd (tell w))
                (funExt λ { tt → branchPath })
            ∙ TargetAppFiller w valuation valuationᴰ
                (λ _ → T.S.app (tell w') (λ _ → T.S.var tt))
            ∙ ΣPathP
                ( WriterFreeModel .snd .fst (tell-tellEq w w') valuation
                , Bᴰ .snd .fst (tell-tellEq w w') valuation valuationᴰ)
            ∙ sym (TargetAppFiller (W._·_ w w') valuation valuationᴰ
                (λ _ → T.S.var tt))
            ∙ T.Algebraᴰ-op-filler (Bᴰ .fst) (tell (W._·_ w w'))
                (λ _ → WriterFreeModelη x) (λ _ → fᴰ x xᴰ)
                (W._·_ w w' , x)
                (ΣPathP (W.·IdR (W._·_ w w') , refl))
            ∙ cong RecᴰTotal sourcePath)
          where
          w' : W .fst
          w' = γ tt .fst

          x : X .fst
          x = γ tt .snd

          xᴰ : Xᴰ x .fst
          xᴰ = γᴰ tt

          valuation : Unit → WriterFreeModel .fst .fst
          valuation _ = WriterFreeModelη x

          valuationᴰ : (u : Unit) → Bᴰ .fst .fst (valuation u)
          valuationᴰ _ = fᴰ x xᴰ

          branchPath : Path (T.∫Algebra (Bᴰ .fst) .fst)
            (γ tt , WriterFreeModelRecᴰ-fun (γ tt) (γᴰ tt))
            ( T.interp (WriterFreeModel .fst) valuation
                (T.S.app (tell w') (λ _ → T.S.var tt))
            , T.interpᴰ (Bᴰ .fst) valuation valuationᴰ
                (T.S.app (tell w') (λ _ → T.S.var tt)))
          branchPath =
            sym (T.Algebraᴰ-op-filler (Bᴰ .fst) (tell w')
              (λ _ → WriterFreeModelη x) (λ _ → fᴰ x xᴰ)
              (w' , x) (ΣPathP (W.·IdR w' , refl)))
            ∙ TargetAppFiller w' valuation valuationᴰ
                (λ _ → T.S.var tt)

          sourcePath : Path (T.∫Algebra WriterFreeAlgebraᴰ .fst)
            ((W._·_ w w' , x) , xᴰ)
            (op⟨γ⟩ , op⟨γᴰ⟩)
          sourcePath =
            R.reind-filler op∘γ≡op⟨γ⟩
            ∙ R.≡in {pth = refl} op∘γᴰ≡op⟨γᴰ⟩

    WriterFreeModelRecᴰ-uniq :
      (Bᴰ : T.Modelᴰ WriterFreeModel ℓD')
      (hᴰ : T.Homoᴰ (T.idHomo {A = WriterFreeModel .fst})
        WriterFreeAlgebraᴰ (Bᴰ .fst))
      → hᴰ .fst ≡
        WriterFreeModelRecᴰ Bᴰ
          (λ x xᴰ → hᴰ .fst
            (WriterFreeModelη x) (WriterFreeModelηᴰ x xᴰ)) .fst
    WriterFreeModelRecᴰ-uniq Bᴰ hᴰ =
      funExt λ { (w , x) → funExt λ xᴰ →
        sym
          (hᴰ .snd (tell w)
            (λ _ → WriterFreeModelη x)
            (λ _ → WriterFreeModelηᴰ x xᴰ)
            (w , x) basePath xᴰ (sourceᴰ≡ w x xᴰ)) }
      where
      basePath : {w : W .fst} {x : X .fst} →
        WriterFreeModel .fst .snd (tell w)
          (λ _ → WriterFreeModelη x) ≡ (w , x)
      basePath {w = w} = ΣPathP (W.·IdR w , refl)

      sourceᴰ≡ : (w : W .fst) (x : X .fst) (xᴰ : Xᴰ x .fst) →
        WriterFreeAlgebraᴰ .snd (tell w)
          (λ _ → WriterFreeModelη x)
          (λ _ → WriterFreeModelηᴰ x xᴰ)
          (w , x) basePath
        ≡ xᴰ
      sourceᴰ≡ w x xᴰ = R.rectifyOut {e' = refl}
        (R.reind-filler⁻ basePath ∙ constantPath)
        where
        constantPath : Path (T.∫Algebra WriterFreeAlgebraᴰ .fst)
          ((W._·_ w W.ε , x) , xᴰ) ((w , x) , xᴰ)
        constantPath i .fst .fst = W.·IdR w i
        constantPath i .fst .snd = x
        constantPath i .snd = xᴰ

    WriterFreeModelUniversalᴰ :
      (Bᴰ : T.Modelᴰ WriterFreeModel ℓD') →
      isEquiv
        (λ (hᴰ : T.Homoᴰ (T.idHomo {A = WriterFreeModel .fst})
            WriterFreeAlgebraᴰ (Bᴰ .fst)) x xᴰ →
          hᴰ .fst (WriterFreeModelη x) (WriterFreeModelηᴰ x xᴰ))
    WriterFreeModelUniversalᴰ Bᴰ = isIsoToIsEquiv
      ( WriterFreeModelRecᴰ Bᴰ
      , (λ fᴰ → funExt λ x → funExt λ xᴰ →
          WriterFreeModelRecᴰ-β Bᴰ fᴰ x xᴰ)
      , (λ hᴰ → Σ≡Prop
          (λ _ → isPropΠ6 λ _ _ _ _ _ _ →
            isPropΠ λ _ → Bᴰ .snd .snd _ _ _)
          (sym (WriterFreeModelRecᴰ-uniq Bᴰ hᴰ)))
      )

    module _ {B : T.Model ℓB}
      (ϕ : T.Homo (WriterFreeModel .fst) (B .fst))
      (Bᴰ : T.Modelᴰ B ℓD')
      (fᴰ : (x : X .fst) → Xᴰ x .fst →
        Bᴰ .fst .fst (ϕ .fst (WriterFreeModelη x)))
      where
      WriterFreeModelRecOverᴰ :
        T.Homoᴰ ϕ WriterFreeAlgebraᴰ (Bᴰ .fst)
      WriterFreeModelRecOverᴰ =
        WriterFreeModelRecᴰ
          (T._*_ {M = WriterFreeModel} {N = B} ϕ Bᴰ) fᴰ

      WriterFreeModelRecOverᴰ-β :
        (x : X .fst) (xᴰ : Xᴰ x .fst) →
        WriterFreeModelRecOverᴰ .fst
          (WriterFreeModelη x) (WriterFreeModelηᴰ x xᴰ) ≡ fᴰ x xᴰ
      WriterFreeModelRecOverᴰ-β =
        WriterFreeModelRecᴰ-β
          (T._*_ {M = WriterFreeModel} {N = B} ϕ Bᴰ) fᴰ

    WriterFreeModelRecOverᴰ-uniq : {B : T.Model ℓB}
      (ϕ : T.Homo (WriterFreeModel .fst) (B .fst))
      (Bᴰ : T.Modelᴰ B ℓD')
      (hᴰ : T.Homoᴰ ϕ WriterFreeAlgebraᴰ (Bᴰ .fst))
      → hᴰ .fst ≡ WriterFreeModelRecOverᴰ {B = B} ϕ Bᴰ
          (λ x xᴰ → hᴰ .fst
            (WriterFreeModelη x) (WriterFreeModelηᴰ x xᴰ)) .fst
    WriterFreeModelRecOverᴰ-uniq {B = B} ϕ Bᴰ =
      WriterFreeModelRecᴰ-uniq
        (T._*_ {M = WriterFreeModel} {N = B} ϕ Bᴰ)

    WriterFreeModelUniversalOverᴰ : {B : T.Model ℓB}
      (ϕ : T.Homo (WriterFreeModel .fst) (B .fst))
      (Bᴰ : T.Modelᴰ B ℓD') →
      isEquiv
        (λ (hᴰ : T.Homoᴰ ϕ WriterFreeAlgebraᴰ (Bᴰ .fst)) x xᴰ →
          hᴰ .fst (WriterFreeModelη x) (WriterFreeModelηᴰ x xᴰ))
    WriterFreeModelUniversalOverᴰ {B = B} ϕ Bᴰ =
      WriterFreeModelUniversalᴰ
        (T._*_ {M = WriterFreeModel} {N = B} ϕ Bᴰ)
