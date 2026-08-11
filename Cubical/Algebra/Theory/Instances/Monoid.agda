-- The algebraic theory of monoids and its concrete free list model.
module Cubical.Algebra.Theory.Instances.Monoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.List
open import Cubical.Data.List.Dependent as ListP
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Theory.Base

private
  variable
    ℓV ℓX ℓB ℓD ℓD' : Level

data MonoidOp : Type ℓ-zero where
  unitOp multOp : MonoidOp

MonoidSignature : Signature ℓ-zero ℓ-zero
MonoidSignature .Signature.Op = MonoidOp
MonoidSignature .Signature.Arity unitOp = ⊥
MonoidSignature .Signature.Arity multOp = Bool

module MonoidSignature where
  open Signature MonoidSignature public

private
  module S = Signature MonoidSignature

  emptyBranches : {A : Type ℓX} → ⊥ → A
  emptyBranches ()

  boolBranches : {A : Type ℓX} → A → A → Bool → A
  boolBranches x y false = x
  boolBranches x y true = y

unitTm : ∀ {V : Type ℓX} → S.|FreeAlgebra| V
unitTm = S.app unitOp emptyBranches

multTm : ∀ {V : Type ℓX} →
  S.|FreeAlgebra| V → S.|FreeAlgebra| V → S.|FreeAlgebra| V
multTm x y = S.app multOp (boolBranches x y)

data AssocVar : Type ℓ-zero where
  leftVar middleVar rightVar : AssocVar

data MonoidEq : Type ℓ-zero where
  unit-lEq unit-rEq assocEq : MonoidEq

MonoidEqArity : MonoidEq → Type ℓ-zero
MonoidEqArity unit-lEq = Unit
MonoidEqArity unit-rEq = Unit
MonoidEqArity assocEq = AssocVar

MonoidLhs : (e : MonoidEq) →
  S.|FreeAlgebra| (MonoidEqArity e)
MonoidLhs unit-lEq = multTm unitTm (S.var tt)
MonoidLhs unit-rEq = multTm (S.var tt) unitTm
MonoidLhs assocEq =
  multTm (S.var leftVar)
    (multTm (S.var middleVar) (S.var rightVar))

MonoidRhs : (e : MonoidEq) →
  S.|FreeAlgebra| (MonoidEqArity e)
MonoidRhs unit-lEq = S.var tt
MonoidRhs unit-rEq = S.var tt
MonoidRhs assocEq =
  multTm (multTm (S.var leftVar) (S.var middleVar))
    (S.var rightVar)

MonoidTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero
MonoidTheory .Theory.S = MonoidSignature
MonoidTheory .Theory.Eq = MonoidEq
MonoidTheory .Theory.EqArity = MonoidEqArity
MonoidTheory .Theory.lhs = MonoidLhs
MonoidTheory .Theory.rhs = MonoidRhs

module MonoidTheory where
  open Theory MonoidTheory public

module _ (B : Theory.Model MonoidTheory ℓB) where
  private
    module T = Theory MonoidTheory

  MonoidModelUnit : B .fst .fst
  MonoidModelUnit = B .fst .snd unitOp emptyBranches

  MonoidModelMult : B .fst .fst → B .fst .fst → B .fst .fst
  MonoidModelMult x y = B .fst .snd multOp (boolBranches x y)

  MonoidInterpUnit : {V : Type ℓV} (ρ : V → B .fst .fst) →
    T.interp (B .fst) ρ unitTm ≡ MonoidModelUnit
  MonoidInterpUnit ρ =
    sym
      (T.recFA (B .fst) ρ .snd unitOp emptyBranches unitTm refl)
    ∙ cong (B .fst .snd unitOp) (funExt λ ())

  MonoidInterpMult : {V : Type ℓV} (ρ : V → B .fst .fst)
    (x y : T.|FreeAlgebra| V) →
    T.interp (B .fst) ρ (multTm x y) ≡
      MonoidModelMult
        (T.interp (B .fst) ρ x) (T.interp (B .fst) ρ y)
  MonoidInterpMult ρ x y =
    sym
      (T.recFA (B .fst) ρ .snd multOp
        (boolBranches x y) (multTm x y) refl)
    ∙ cong (B .fst .snd multOp)
        (funExt λ { false → refl ; true → refl })

  MonoidModelUnitL : (x : B .fst .fst) →
    MonoidModelMult MonoidModelUnit x ≡ x
  MonoidModelUnitL x =
    cong (λ u → MonoidModelMult u x)
      (sym (MonoidInterpUnit (λ _ → x)))
    ∙ sym (MonoidInterpMult (λ _ → x) unitTm (S.var tt))
    ∙ B .snd .fst unit-lEq (λ _ → x)

  MonoidModelUnitR : (x : B .fst .fst) →
    MonoidModelMult x MonoidModelUnit ≡ x
  MonoidModelUnitR x =
    cong (MonoidModelMult x)
      (sym (MonoidInterpUnit (λ _ → x)))
    ∙ sym (MonoidInterpMult (λ _ → x) (S.var tt) unitTm)
    ∙ B .snd .fst unit-rEq (λ _ → x)

  MonoidModelAssoc : (x y z : B .fst .fst) →
    MonoidModelMult x (MonoidModelMult y z) ≡
      MonoidModelMult (MonoidModelMult x y) z
  MonoidModelAssoc x y z =
    cong (MonoidModelMult x)
      (sym (MonoidInterpMult valuation
        (S.var middleVar) (S.var rightVar)))
    ∙ sym (MonoidInterpMult valuation
        (S.var leftVar)
        (multTm (S.var middleVar) (S.var rightVar)))
    ∙ B .snd .fst assocEq valuation
    ∙ MonoidInterpMult valuation
        (multTm (S.var leftVar) (S.var middleVar))
        (S.var rightVar)
    ∙ cong (λ xy → MonoidModelMult xy z)
        (MonoidInterpMult valuation
          (S.var leftVar) (S.var middleVar))
    where
    valuation : AssocVar → B .fst .fst
    valuation leftVar = x
    valuation middleVar = y
    valuation rightVar = z

module _ (X : hSet ℓX) where
  private
    module T = Theory MonoidTheory

  ListFreeModel : T.Model ℓX
  ListFreeModel .fst .fst = List (X .fst)
  ListFreeModel .fst .snd unitOp γ = []
  ListFreeModel .fst .snd multOp γ = γ false ++ γ true
  ListFreeModel .snd .fst unit-lEq ρ = refl
  ListFreeModel .snd .fst unit-rEq ρ = ++-unit-r (ρ tt)
  ListFreeModel .snd .fst assocEq ρ =
    sym (++-assoc (ρ leftVar) (ρ middleVar) (ρ rightVar))
  ListFreeModel .snd .snd = isOfHLevelList 0 (X .snd)

  ListFreeModelη : X .fst → ListFreeModel .fst .fst
  ListFreeModelη x = [ x ]

  module _ (B : T.Model ℓB) (f : X .fst → B .fst .fst) where
    ListFreeModelRec-fun : List (X .fst) → B .fst .fst
    ListFreeModelRec-fun =
      foldr (λ x b → MonoidModelMult B (f x) b) (MonoidModelUnit B)

    ListFreeModelRec-++ : (xs ys : List (X .fst)) →
      ListFreeModelRec-fun (xs ++ ys) ≡
        MonoidModelMult B
          (ListFreeModelRec-fun xs) (ListFreeModelRec-fun ys)
    ListFreeModelRec-++ [] ys =
      sym (MonoidModelUnitL B (ListFreeModelRec-fun ys))
    ListFreeModelRec-++ (x ∷ xs) ys =
      cong (MonoidModelMult B (f x)) (ListFreeModelRec-++ xs ys)
      ∙ MonoidModelAssoc B (f x)
          (ListFreeModelRec-fun xs) (ListFreeModelRec-fun ys)

    ListFreeModelRec : T.Homo (ListFreeModel .fst) (B .fst)
    ListFreeModelRec .fst = ListFreeModelRec-fun
    ListFreeModelRec .snd unitOp γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      cong (B .fst .snd unitOp) (funExt λ ())
      ∙ cong ListFreeModelRec-fun op∘γ≡op⟨γ⟩
    ListFreeModelRec .snd multOp γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      cong (B .fst .snd multOp)
        (funExt λ { false → refl ; true → refl })
      ∙ sym (ListFreeModelRec-++ (γ false) (γ true))
      ∙ cong ListFreeModelRec-fun op∘γ≡op⟨γ⟩

    ListFreeModelRec-β : (x : X .fst) →
      ListFreeModelRec .fst (ListFreeModelη x) ≡ f x
    ListFreeModelRec-β x = MonoidModelUnitR B (f x)

  ListFreeModelRec-uniq :
    (B : T.Model ℓB)
    (h : T.Homo (ListFreeModel .fst) (B .fst))
    → h .fst ≡
      ListFreeModelRec B (λ x → h .fst (ListFreeModelη x)) .fst
  ListFreeModelRec-uniq B h = funExt go
    where
    go : (xs : List (X .fst)) →
      h .fst xs ≡
        ListFreeModelRec B
          (λ x → h .fst (ListFreeModelη x)) .fst xs
    go [] =
      sym (h .snd unitOp (λ ()) [] refl)
      ∙ cong (B .fst .snd unitOp) (funExt λ ())
    go (x ∷ xs) =
      sym
        (h .snd multOp
          (λ { false → ListFreeModelη x ; true → xs })
          (x ∷ xs) refl)
      ∙ cong (B .fst .snd multOp)
          (funExt λ { false → refl ; true → refl })
      ∙ cong (MonoidModelMult B (h .fst (ListFreeModelη x))) (go xs)

  ListFreeModelUniversal : (B : T.Model ℓB) →
    isEquiv
      (λ (h : T.Homo (ListFreeModel .fst) (B .fst)) x →
        h .fst (ListFreeModelη x))
  ListFreeModelUniversal B = isIsoToIsEquiv
    ( ListFreeModelRec B
    , (λ f → funExt (ListFreeModelRec-β B f))
    , (λ h → Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → B .snd .snd _ _)
        (sym (ListFreeModelRec-uniq B h)))
    )

  module _ (Xᴰ : X .fst → hSet ℓD) where
    private
      module R = hSetReasoning
        (ListFreeModel .fst .fst , ListFreeModel .snd .snd)
        (λ xs → ListP (λ x → Xᴰ x .fst) xs)

    appendListP : {xs ys : List (X .fst)} →
      ListP (λ x → Xᴰ x .fst) xs →
      ListP (λ x → Xᴰ x .fst) ys →
      ListP (λ x → Xᴰ x .fst) (xs ++ ys)
    appendListP ListP.[] ysᴰ = ysᴰ
    appendListP (ListP._∷_ xᴰ xsᴰ) ysᴰ =
      ListP._∷_ xᴰ (appendListP xsᴰ ysᴰ)

    ListFreeAlgebraᴰ :
      T.Algebraᴰ (ListFreeModel .fst) (ℓ-max ℓX ℓD)
    ListFreeAlgebraᴰ .fst xs = ListP (λ x → Xᴰ x .fst) xs
    ListFreeAlgebraᴰ .snd unitOp γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      R.reind op∘γ≡op⟨γ⟩ ListP.[]
    ListFreeAlgebraᴰ .snd multOp γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      R.reind op∘γ≡op⟨γ⟩
        (appendListP (γᴰ false) (γᴰ true))

    ListUnitNormalize :
      (γ : ⊥ → ListFreeModel .fst .fst)
      (γᴰ : (v : ⊥) → ListFreeAlgebraᴰ .fst (γ v)) →
      Path (T.∫Algebra ListFreeAlgebraᴰ .fst)
        ( ListFreeModel .fst .snd unitOp γ
        , ListFreeAlgebraᴰ .snd unitOp γ γᴰ _ refl)
        ([] , ListP.[])
    ListUnitNormalize γ γᴰ = R.reind-filler⁻ refl

    ListMultNormalize :
      (γ : Bool → ListFreeModel .fst .fst)
      (γᴰ : (v : Bool) → ListFreeAlgebraᴰ .fst (γ v)) →
      Path (T.∫Algebra ListFreeAlgebraᴰ .fst)
        ( ListFreeModel .fst .snd multOp γ
        , ListFreeAlgebraᴰ .snd multOp γ γᴰ _ refl)
        ( γ false ++ γ true
        , appendListP (γᴰ false) (γᴰ true))
    ListMultNormalize γ γᴰ = R.reind-filler⁻ refl

    ListAppFiller : {V : Type ℓV}
      (op : MonoidOp)
      (ρ : V → ListFreeModel .fst .fst)
      (ρᴰ : (v : V) → ListFreeAlgebraᴰ .fst (ρ v))
      (γ : T.Arity op → T.|FreeAlgebra| V) →
      Path (T.∫Algebra ListFreeAlgebraᴰ .fst)
        ( ListFreeModel .fst .snd op
            (λ v → T.interp (ListFreeModel .fst) ρ (γ v))
        , ListFreeAlgebraᴰ .snd op
            (λ v → T.interp (ListFreeModel .fst) ρ (γ v))
            (λ v → T.interpᴰ ListFreeAlgebraᴰ ρ ρᴰ (γ v))
            _ refl)
        ( T.interp (ListFreeModel .fst) ρ (T.S.app op γ)
        , T.interpᴰ ListFreeAlgebraᴰ ρ ρᴰ (T.S.app op γ))
    ListAppFiller op ρ ρᴰ γ =
      T.Algebraᴰ-op-filler ListFreeAlgebraᴰ op
        (λ v → T.interp (ListFreeModel .fst) ρ (γ v))
        (λ v → T.interpᴰ ListFreeAlgebraᴰ ρ ρᴰ (γ v))
        (T.interp (ListFreeModel .fst) ρ (T.S.app op γ))
        (T.recFA (ListFreeModel .fst) ρ .snd op γ
          (T.S.app op γ) refl)

    ListUnitInterpPath : {V : Type ℓV}
      (ρ : V → ListFreeModel .fst .fst)
      (ρᴰ : (v : V) → ListFreeAlgebraᴰ .fst (ρ v)) →
      Path (T.∫Algebra ListFreeAlgebraᴰ .fst)
        ( T.interp (ListFreeModel .fst) ρ unitTm
        , T.interpᴰ ListFreeAlgebraᴰ ρ ρᴰ unitTm)
        ([] , ListP.[])
    ListUnitInterpPath ρ ρᴰ =
      sym (ListAppFiller unitOp ρ ρᴰ emptyBranches)
      ∙ ListUnitNormalize
          (λ v → T.interp (ListFreeModel .fst) ρ (emptyBranches v))
          (λ v → T.interpᴰ ListFreeAlgebraᴰ ρ ρᴰ
            (emptyBranches v))

    ListMultInterpPath : {V : Type ℓV}
      (ρ : V → ListFreeModel .fst .fst)
      (ρᴰ : (v : V) → ListFreeAlgebraᴰ .fst (ρ v))
      (x y : T.|FreeAlgebra| V) →
      Path (T.∫Algebra ListFreeAlgebraᴰ .fst)
        ( T.interp (ListFreeModel .fst) ρ (multTm x y)
        , T.interpᴰ ListFreeAlgebraᴰ ρ ρᴰ (multTm x y))
        ( T.interp (ListFreeModel .fst) ρ x ++
            T.interp (ListFreeModel .fst) ρ y
        , appendListP
            (T.interpᴰ ListFreeAlgebraᴰ ρ ρᴰ x)
            (T.interpᴰ ListFreeAlgebraᴰ ρ ρᴰ y))
    ListMultInterpPath ρ ρᴰ x y =
      sym (ListAppFiller multOp ρ ρᴰ (boolBranches x y))
      ∙ ListMultNormalize
          (λ v → T.interp (ListFreeModel .fst) ρ
            (boolBranches x y v))
          (λ v → T.interpᴰ ListFreeAlgebraᴰ ρ ρᴰ
            (boolBranches x y v))

    ListPAppendTotal :
      T.∫Algebra ListFreeAlgebraᴰ .fst →
      T.∫Algebra ListFreeAlgebraᴰ .fst →
      T.∫Algebra ListFreeAlgebraᴰ .fst
    ListPAppendTotal (xs , xsᴰ) (ys , ysᴰ) =
      xs ++ ys , appendListP xsᴰ ysᴰ

    ListPAppendUnitR : {xs : List (X .fst)}
      (xsᴰ : ListP (λ x → Xᴰ x .fst) xs) →
      Path (T.∫Algebra ListFreeAlgebraᴰ .fst)
        (ListPAppendTotal (xs , xsᴰ) ([] , ListP.[]))
        (xs , xsᴰ)
    ListPAppendUnitR {xs = []} ListP.[] = refl
    ListPAppendUnitR {xs = x ∷ xs} (ListP._∷_ xᴰ xsᴰ) =
      cong (λ z → x ∷ z .fst , ListP._∷_ xᴰ (z .snd))
        (ListPAppendUnitR xsᴰ)

    ListPAppendAssoc : {xs ys zs : List (X .fst)}
      (xsᴰ : ListP (λ x → Xᴰ x .fst) xs)
      (ysᴰ : ListP (λ x → Xᴰ x .fst) ys)
      (zsᴰ : ListP (λ x → Xᴰ x .fst) zs) →
      Path (T.∫Algebra ListFreeAlgebraᴰ .fst)
        (ListPAppendTotal (xs , xsᴰ)
          (ListPAppendTotal (ys , ysᴰ) (zs , zsᴰ)))
        (ListPAppendTotal
          (ListPAppendTotal (xs , xsᴰ) (ys , ysᴰ)) (zs , zsᴰ))
    ListPAppendAssoc {xs = []} ListP.[] ysᴰ zsᴰ = refl
    ListPAppendAssoc {xs = x ∷ xs}
      (ListP._∷_ xᴰ xsᴰ) ysᴰ zsᴰ =
      cong (λ z → x ∷ z .fst , ListP._∷_ xᴰ (z .snd))
        (ListPAppendAssoc xsᴰ ysᴰ zsᴰ)

    ListFreeModelᴰ :
      T.Modelᴰ ListFreeModel (ℓ-max ℓX ℓD)
    ListFreeModelᴰ .fst = ListFreeAlgebraᴰ
    ListFreeModelᴰ .snd .fst unit-lEq ρ ρᴰ =
      R.rectifyOut {e' = ListFreeModel .snd .fst unit-lEq ρ}
        ( ListMultInterpPath ρ ρᴰ unitTm (T.S.var tt)
        ∙ cong (λ z → ListPAppendTotal z (ρ tt , ρᴰ tt))
            (ListUnitInterpPath ρ ρᴰ))
    ListFreeModelᴰ .snd .fst unit-rEq ρ ρᴰ =
      R.rectifyOut {e' = ListFreeModel .snd .fst unit-rEq ρ}
        ( ListMultInterpPath ρ ρᴰ (T.S.var tt) unitTm
        ∙ cong (ListPAppendTotal (ρ tt , ρᴰ tt))
            (ListUnitInterpPath ρ ρᴰ)
        ∙ ListPAppendUnitR (ρᴰ tt))
    ListFreeModelᴰ .snd .fst assocEq ρ ρᴰ =
      R.rectifyOut {e' = ListFreeModel .snd .fst assocEq ρ}
        ( ListMultInterpPath ρ ρᴰ (T.S.var leftVar)
            (multTm (T.S.var middleVar) (T.S.var rightVar))
        ∙ cong (ListPAppendTotal (ρ leftVar , ρᴰ leftVar))
            (ListMultInterpPath ρ ρᴰ
              (T.S.var middleVar) (T.S.var rightVar))
        ∙ ListPAppendAssoc
            (ρᴰ leftVar) (ρᴰ middleVar) (ρᴰ rightVar)
        ∙ cong (λ z → ListPAppendTotal z (ρ rightVar , ρᴰ rightVar))
            (sym (ListMultInterpPath ρ ρᴰ
              (T.S.var leftVar) (T.S.var middleVar)))
        ∙ sym (ListMultInterpPath ρ ρᴰ
            (multTm (T.S.var leftVar) (T.S.var middleVar))
            (T.S.var rightVar)))
    ListFreeModelᴰ .snd .snd xs =
      isOfHLevelSucSuc-ListP 0 (λ x → Xᴰ x .snd)

    ListFreeModelηᴰ : (x : X .fst) → Xᴰ x .fst →
      ListFreeModelᴰ .fst .fst (ListFreeModelη x)
    ListFreeModelηᴰ x xᴰ = ListP._∷_ xᴰ ListP.[]

    module _
      (Bᴰ : T.Modelᴰ ListFreeModel ℓD')
      (fᴰ : (x : X .fst) → Xᴰ x .fst →
        Bᴰ .fst .fst (ListFreeModelη x))
      where
      private
        TargetModel : T.Model (ℓ-max ℓX ℓD')
        TargetModel = T.∫Model {M = ListFreeModel} Bᴰ

        module BᴰR = hSetReasoning
          (ListFreeModel .fst .fst , ListFreeModel .snd .snd)
          (Bᴰ .fst .fst)

      ListFreeModelRecᴰ-fun :
        (xs : ListFreeModel .fst .fst) →
        ListFreeAlgebraᴰ .fst xs → Bᴰ .fst .fst xs
      ListFreeModelRecᴰ-fun [] ListP.[] =
        MonoidModelUnit TargetModel .snd
      ListFreeModelRecᴰ-fun (x ∷ xs) (ListP._∷_ xᴰ xsᴰ) =
        MonoidModelMult TargetModel
          (ListFreeModelη x , fᴰ x xᴰ)
          (xs , ListFreeModelRecᴰ-fun xs xsᴰ) .snd

      private
        RecᴰTotal : T.∫Algebra ListFreeAlgebraᴰ .fst →
          TargetModel .fst .fst
        RecᴰTotal (xs , xsᴰ) = xs , ListFreeModelRecᴰ-fun xs xsᴰ

      ListFreeModelRecᴰ-++ : {xs ys : List (X .fst)}
        (xsᴰ : ListP (λ x → Xᴰ x .fst) xs)
        (ysᴰ : ListP (λ x → Xᴰ x .fst) ys) →
        Path (TargetModel .fst .fst)
          ( RecᴰTotal
              (xs ++ ys , appendListP xsᴰ ysᴰ))
          ( MonoidModelMult TargetModel
              (RecᴰTotal (xs , xsᴰ)) (RecᴰTotal (ys , ysᴰ)))
      ListFreeModelRecᴰ-++ ListP.[] ysᴰ =
        sym (MonoidModelUnitL TargetModel (RecᴰTotal (_ , ysᴰ)))
      ListFreeModelRecᴰ-++
        (ListP._∷_ {x = x} xᴰ xsᴰ) ysᴰ =
        cong (MonoidModelMult TargetModel
          (ListFreeModelη x , fᴰ x xᴰ))
          (ListFreeModelRecᴰ-++ xsᴰ ysᴰ)
        ∙ MonoidModelAssoc TargetModel
            (ListFreeModelη x , fᴰ x xᴰ)
            (RecᴰTotal (_ , xsᴰ)) (RecᴰTotal (_ , ysᴰ))

      ListFreeModelRecᴰ-β : (x : X .fst) (xᴰ : Xᴰ x .fst) →
        ListFreeModelRecᴰ-fun
          (ListFreeModelη x) (ListFreeModelηᴰ x xᴰ) ≡ fᴰ x xᴰ
      ListFreeModelRecᴰ-β x xᴰ = BᴰR.rectifyOut {e' = refl}
        (MonoidModelUnitR TargetModel (ListFreeModelη x , fᴰ x xᴰ))

      private
        ListFreeModelRecᴰ-pres-unit :
          (γ : ⊥ → ListFreeModel .fst .fst)
          (γᴰ : (v : ⊥) → ListFreeAlgebraᴰ .fst (γ v)) →
          Path (TargetModel .fst .fst)
            ( ListFreeModel .fst .snd unitOp γ
            , Bᴰ .fst .snd unitOp γ
                (λ v → ListFreeModelRecᴰ-fun (γ v) (γᴰ v))
                _ refl)
            (RecᴰTotal
              ( ListFreeModel .fst .snd unitOp γ
              , ListFreeAlgebraᴰ .snd unitOp γ γᴰ _ refl))
        ListFreeModelRecᴰ-pres-unit γ γᴰ =
          cong (T.∫Algebra (Bᴰ .fst) .snd unitOp) (funExt λ ())
          ∙ cong RecᴰTotal (sym (ListUnitNormalize γ γᴰ))

        ListFreeModelRecᴰ-pres-mult :
          (γ : Bool → ListFreeModel .fst .fst)
          (γᴰ : (v : Bool) → ListFreeAlgebraᴰ .fst (γ v)) →
          Path (TargetModel .fst .fst)
            ( ListFreeModel .fst .snd multOp γ
            , Bᴰ .fst .snd multOp γ
                (λ v → ListFreeModelRecᴰ-fun (γ v) (γᴰ v))
                _ refl)
            (RecᴰTotal
              ( ListFreeModel .fst .snd multOp γ
              , ListFreeAlgebraᴰ .snd multOp γ γᴰ _ refl))
        ListFreeModelRecᴰ-pres-mult γ γᴰ =
          cong (T.∫Algebra (Bᴰ .fst) .snd multOp)
            (funExt λ { false → refl ; true → refl })
          ∙ sym (ListFreeModelRecᴰ-++ (γᴰ false) (γᴰ true))
          ∙ cong RecᴰTotal (sym (ListMultNormalize γ γᴰ))

      ListFreeModelRecᴰ :
        T.Homoᴰ (T.idHomo {A = ListFreeModel .fst})
          ListFreeAlgebraᴰ (Bᴰ .fst)
      ListFreeModelRecᴰ .fst = ListFreeModelRecᴰ-fun
      ListFreeModelRecᴰ .snd unitOp γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
        op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
          BᴰR.rectifyOut {e' = refl}
            ( sym (T.Algebraᴰ-op-filler (Bᴰ .fst) unitOp γ
                (λ v → ListFreeModelRecᴰ-fun (γ v) (γᴰ v))
                op⟨γ⟩ op∘γ≡op⟨γ⟩)
            ∙ ListFreeModelRecᴰ-pres-unit γ γᴰ
            ∙ cong RecᴰTotal sourcePath)
        where
        sourcePath : Path (T.∫Algebra ListFreeAlgebraᴰ .fst)
          ( ListFreeModel .fst .snd unitOp γ
          , ListFreeAlgebraᴰ .snd unitOp γ γᴰ _ refl)
          (op⟨γ⟩ , op⟨γᴰ⟩)
        sourcePath =
          T.Algebraᴰ-op-filler ListFreeAlgebraᴰ unitOp γ γᴰ
            op⟨γ⟩ op∘γ≡op⟨γ⟩
          ∙ R.≡in {pth = refl} op∘γᴰ≡op⟨γᴰ⟩
      ListFreeModelRecᴰ .snd multOp γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
        op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
          BᴰR.rectifyOut {e' = refl}
            ( sym (T.Algebraᴰ-op-filler (Bᴰ .fst) multOp γ
                (λ v → ListFreeModelRecᴰ-fun (γ v) (γᴰ v))
                op⟨γ⟩ op∘γ≡op⟨γ⟩)
            ∙ ListFreeModelRecᴰ-pres-mult γ γᴰ
            ∙ cong RecᴰTotal sourcePath)
        where
        sourcePath : Path (T.∫Algebra ListFreeAlgebraᴰ .fst)
          ( ListFreeModel .fst .snd multOp γ
          , ListFreeAlgebraᴰ .snd multOp γ γᴰ _ refl)
          (op⟨γ⟩ , op⟨γᴰ⟩)
        sourcePath =
          T.Algebraᴰ-op-filler ListFreeAlgebraᴰ multOp γ γᴰ
            op⟨γ⟩ op∘γ≡op⟨γ⟩
          ∙ R.≡in {pth = refl} op∘γᴰ≡op⟨γᴰ⟩

    ListFreeModelRecᴰ-uniq :
      (Bᴰ : T.Modelᴰ ListFreeModel ℓD')
      (hᴰ : T.Homoᴰ (T.idHomo {A = ListFreeModel .fst})
        ListFreeAlgebraᴰ (Bᴰ .fst)) →
      hᴰ .fst ≡
        ListFreeModelRecᴰ Bᴰ
          (λ x xᴰ → hᴰ .fst
            (ListFreeModelη x) (ListFreeModelηᴰ x xᴰ)) .fst
    ListFreeModelRecᴰ-uniq Bᴰ hᴰ =
      funExt λ xs → funExt λ xsᴰ →
        BᴰR.rectifyOut {e' = refl} (totalPath xs xsᴰ)
      where
      TargetModel : T.Model _
      TargetModel = T.∫Model {M = ListFreeModel} Bᴰ

      module BᴰR = hSetReasoning
        (ListFreeModel .fst .fst , ListFreeModel .snd .snd)
        (Bᴰ .fst .fst)

      HomoᴰTotal : T.Homo
        (T.∫Algebra ListFreeAlgebraᴰ)
        (TargetModel .fst)
      HomoᴰTotal .fst z = z .fst , hᴰ .fst (z .fst) (z .snd)
      HomoᴰTotal .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
        T.Algebraᴰ-op-filler (Bᴰ .fst) op
          (λ v → γ v .fst)
          (λ v → hᴰ .fst (γ v .fst) (γ v .snd))
          (op⟨γ⟩ .fst) basePath
        ∙ BᴰR.≡in {pth = refl}
            (hᴰ .snd op
              (λ v → γ v .fst) (λ v → γ v .snd)
              (op⟨γ⟩ .fst) basePath (op⟨γ⟩ .snd) sourceᴰ≡)
        where
        basePath : ListFreeModel .fst .snd op (λ v → γ v .fst) ≡
          op⟨γ⟩ .fst
        basePath i = op∘γ≡op⟨γ⟩ i .fst

        sourceᴰ≡ :
          ListFreeAlgebraᴰ .snd op
            (λ v → γ v .fst) (λ v → γ v .snd)
            (op⟨γ⟩ .fst) basePath
          ≡ op⟨γ⟩ .snd
        sourceᴰ≡ = R.rectifyOut {e' = refl}
          ( sym (T.Algebraᴰ-op-filler ListFreeAlgebraᴰ op
              (λ v → γ v .fst) (λ v → γ v .snd)
              (op⟨γ⟩ .fst) basePath)
          ∙ op∘γ≡op⟨γ⟩)

      generator : (x : X .fst) (xᴰ : Xᴰ x .fst) →
        T.∫Algebra ListFreeAlgebraᴰ .fst
      generator x xᴰ = ListFreeModelη x , ListFreeModelηᴰ x xᴰ

      totalPath : (xs : List (X .fst))
        (xsᴰ : ListFreeAlgebraᴰ .fst xs) →
        Path (TargetModel .fst .fst)
          (xs , hᴰ .fst xs xsᴰ)
          ( xs
          , ListFreeModelRecᴰ Bᴰ
              (λ x xᴰ → hᴰ .fst
                (ListFreeModelη x) (ListFreeModelηᴰ x xᴰ))
              .fst xs xsᴰ)
      totalPath [] ListP.[] =
        sym (HomoᴰTotal .snd unitOp emptySource
          ([] , ListP.[]) unitSourcePath)
        ∙ cong (TargetModel .fst .snd unitOp) (funExt λ ())
        where
        emptySource : ⊥ → T.∫Algebra ListFreeAlgebraᴰ .fst
        emptySource = emptyBranches

        unitSourcePath :
          T.∫Algebra ListFreeAlgebraᴰ .snd unitOp emptySource ≡
            ([] , ListP.[])
        unitSourcePath = ListUnitNormalize
          (λ v → emptySource v .fst) (λ v → emptySource v .snd)
      totalPath (x ∷ xs) (ListP._∷_ xᴰ xsᴰ) =
        sym (HomoᴰTotal .snd multOp sourceBranches
          (x ∷ xs , ListP._∷_ xᴰ xsᴰ) sourceNormalize)
        ∙ cong (TargetModel .fst .snd multOp)
            (funExt λ { false → refl ; true → refl })
        ∙ cong (MonoidModelMult TargetModel
            (ListFreeModelη x , hᴰ .fst
              (ListFreeModelη x) (ListFreeModelηᴰ x xᴰ)))
            (totalPath xs xsᴰ)
        where
        sourceBranches : Bool → T.∫Algebra ListFreeAlgebraᴰ .fst
        sourceBranches = boolBranches (generator x xᴰ) (xs , xsᴰ)

        sourceNormalize :
          T.∫Algebra ListFreeAlgebraᴰ .snd multOp sourceBranches ≡
            (x ∷ xs , ListP._∷_ xᴰ xsᴰ)
        sourceNormalize = ListMultNormalize
          (λ v → sourceBranches v .fst)
          (λ v → sourceBranches v .snd)

    ListFreeModelUniversalᴰ :
      (Bᴰ : T.Modelᴰ ListFreeModel ℓD') →
      isEquiv
        (λ (hᴰ : T.Homoᴰ (T.idHomo {A = ListFreeModel .fst})
            ListFreeAlgebraᴰ (Bᴰ .fst)) x xᴰ →
          hᴰ .fst (ListFreeModelη x) (ListFreeModelηᴰ x xᴰ))
    ListFreeModelUniversalᴰ Bᴰ = isIsoToIsEquiv
      ( ListFreeModelRecᴰ Bᴰ
      , (λ fᴰ → funExt λ x → funExt λ xᴰ →
          ListFreeModelRecᴰ-β Bᴰ fᴰ x xᴰ)
      , (λ hᴰ → Σ≡Prop
          (λ _ → isPropΠ6 λ _ _ _ _ _ _ →
            isPropΠ λ _ → Bᴰ .snd .snd _ _ _)
          (sym (ListFreeModelRecᴰ-uniq Bᴰ hᴰ)))
      )

    module _ {B : T.Model ℓB}
      (ϕ : T.Homo (ListFreeModel .fst) (B .fst))
      (Bᴰ : T.Modelᴰ B ℓD')
      (fᴰ : (x : X .fst) → Xᴰ x .fst →
        Bᴰ .fst .fst (ϕ .fst (ListFreeModelη x)))
      where
      ListFreeModelRecOverᴰ :
        T.Homoᴰ ϕ ListFreeAlgebraᴰ (Bᴰ .fst)
      ListFreeModelRecOverᴰ =
        ListFreeModelRecᴰ
          (T._*_ {M = ListFreeModel} {N = B} ϕ Bᴰ) fᴰ

      ListFreeModelRecOverᴰ-β :
        (x : X .fst) (xᴰ : Xᴰ x .fst) →
        ListFreeModelRecOverᴰ .fst
          (ListFreeModelη x) (ListFreeModelηᴰ x xᴰ) ≡ fᴰ x xᴰ
      ListFreeModelRecOverᴰ-β =
        ListFreeModelRecᴰ-β
          (T._*_ {M = ListFreeModel} {N = B} ϕ Bᴰ) fᴰ

    ListFreeModelRecOverᴰ-uniq : {B : T.Model ℓB}
      (ϕ : T.Homo (ListFreeModel .fst) (B .fst))
      (Bᴰ : T.Modelᴰ B ℓD')
      (hᴰ : T.Homoᴰ ϕ ListFreeAlgebraᴰ (Bᴰ .fst)) →
      hᴰ .fst ≡ ListFreeModelRecOverᴰ {B = B} ϕ Bᴰ
        (λ x xᴰ → hᴰ .fst
          (ListFreeModelη x) (ListFreeModelηᴰ x xᴰ)) .fst
    ListFreeModelRecOverᴰ-uniq {B = B} ϕ Bᴰ =
      ListFreeModelRecᴰ-uniq
        (T._*_ {M = ListFreeModel} {N = B} ϕ Bᴰ)

    ListFreeModelUniversalOverᴰ : {B : T.Model ℓB}
      (ϕ : T.Homo (ListFreeModel .fst) (B .fst))
      (Bᴰ : T.Modelᴰ B ℓD') →
      isEquiv
        (λ (hᴰ : T.Homoᴰ ϕ ListFreeAlgebraᴰ (Bᴰ .fst)) x xᴰ →
          hᴰ .fst (ListFreeModelη x) (ListFreeModelηᴰ x xᴰ))
    ListFreeModelUniversalOverᴰ {B = B} ϕ Bᴰ =
      ListFreeModelUniversalᴰ
        (T._*_ {M = ListFreeModel} {N = B} ϕ Bᴰ)
