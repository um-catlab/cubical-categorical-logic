-- The algebraic theory of monoids and its concrete free list model.
module Cubical.Algebra.Theory.Instances.Monoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.List
open import Cubical.Data.List.Dependent as ListP
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Data.List.More

open import Cubical.Algebra.Theory.Base

private
  variable
    ℓV ℓX ℓXᴰ ℓB ℓD ℓD' : Level

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

  MonoidModelUnit : ⟨ B .fst ⟩
  MonoidModelUnit = B .snd .fst unitOp emptyBranches

  MonoidModelMult : ⟨ B .fst ⟩ → ⟨ B .fst ⟩ → ⟨ B .fst ⟩
  MonoidModelMult x y = B .snd .fst multOp (boolBranches x y)

  MonoidInterpUnit : {V : Type ℓV} (ρ : V → ⟨ B .fst ⟩) →
    T.interp (T.Model→Algebra B) ρ unitTm ≡ MonoidModelUnit
  MonoidInterpUnit ρ =
    sym
      (T.recFA (T.Model→Algebra B) ρ .snd unitOp emptyBranches unitTm refl)
    ∙ cong (B .snd .fst unitOp) (funExt λ ())

  MonoidInterpMult : {V : Type ℓV} (ρ : V → ⟨ B .fst ⟩)
    (x y : T.|FreeAlgebra| V) →
    T.interp (T.Model→Algebra B) ρ (multTm x y) ≡
      MonoidModelMult
        (T.interp (T.Model→Algebra B) ρ x) (T.interp (T.Model→Algebra B) ρ y)
  MonoidInterpMult ρ x y =
    sym
      (T.recFA (T.Model→Algebra B) ρ .snd multOp
        (boolBranches x y) (multTm x y) refl)
    ∙ cong (B .snd .fst multOp)
        (funExt λ { false → refl ; true → refl })

  MonoidModelUnitL : (x : ⟨ B .fst ⟩) →
    MonoidModelMult MonoidModelUnit x ≡ x
  MonoidModelUnitL x =
    cong (λ u → MonoidModelMult u x)
      (sym (MonoidInterpUnit (λ _ → x)))
    ∙ sym (MonoidInterpMult (λ _ → x) unitTm (S.var tt))
    ∙ B .snd .snd unit-lEq (λ _ → x)

  MonoidModelUnitR : (x : ⟨ B .fst ⟩) →
    MonoidModelMult x MonoidModelUnit ≡ x
  MonoidModelUnitR x =
    cong (MonoidModelMult x)
      (sym (MonoidInterpUnit (λ _ → x)))
    ∙ sym (MonoidInterpMult (λ _ → x) (S.var tt) unitTm)
    ∙ B .snd .snd unit-rEq (λ _ → x)

  MonoidModelAssoc : (x y z : ⟨ B .fst ⟩) →
    MonoidModelMult x (MonoidModelMult y z) ≡
      MonoidModelMult (MonoidModelMult x y) z
  MonoidModelAssoc x y z =
    cong (MonoidModelMult x)
      (sym (MonoidInterpMult valuation
        (S.var middleVar) (S.var rightVar)))
    ∙ sym (MonoidInterpMult valuation
        (S.var leftVar)
        (multTm (S.var middleVar) (S.var rightVar)))
    ∙ B .snd .snd assocEq valuation
    ∙ MonoidInterpMult valuation
        (multTm (S.var leftVar) (S.var middleVar))
        (S.var rightVar)
    ∙ cong (λ xy → MonoidModelMult xy z)
        (MonoidInterpMult valuation
          (S.var leftVar) (S.var middleVar))
    where
    valuation : AssocVar → ⟨ B .fst ⟩
    valuation leftVar = x
    valuation middleVar = y
    valuation rightVar = z

module _ (X : hSet ℓX) where
  private
    module T = Theory MonoidTheory

  ListFreeModel : T.Model ℓX
  ListFreeModel .fst = List (X .fst) , isOfHLevelList 0 (X .snd)
  ListFreeModel .snd .fst unitOp γ = []
  ListFreeModel .snd .fst multOp γ = γ false ++ γ true
  ListFreeModel .snd .snd unit-lEq ρ = refl
  ListFreeModel .snd .snd unit-rEq ρ = ++-unit-r (ρ tt)
  ListFreeModel .snd .snd assocEq ρ =
    sym (++-assoc (ρ leftVar) (ρ middleVar) (ρ rightVar))

  ListFreeModelη : X .fst → ⟨ ListFreeModel .fst ⟩
  ListFreeModelη x = [ x ]

  module _ (B : T.Model ℓB) (f : X .fst → ⟨ B .fst ⟩) where
    ListFreeModelRec-fun : List (X .fst) → ⟨ B .fst ⟩
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

    ListFreeModelRec :
      T.Homo (T.Model→Algebra ListFreeModel) (T.Model→Algebra B)
    ListFreeModelRec .fst = ListFreeModelRec-fun
    ListFreeModelRec .snd unitOp γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      cong (B .snd .fst unitOp) (funExt λ ())
      ∙ cong ListFreeModelRec-fun op∘γ≡op⟨γ⟩
    ListFreeModelRec .snd multOp γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      cong (B .snd .fst multOp)
        (funExt λ { false → refl ; true → refl })
      ∙ sym (ListFreeModelRec-++ (γ false) (γ true))
      ∙ cong ListFreeModelRec-fun op∘γ≡op⟨γ⟩

    ListFreeModelRec-β : (x : X .fst) →
      ListFreeModelRec .fst (ListFreeModelη x) ≡ f x
    ListFreeModelRec-β x = MonoidModelUnitR B (f x)

  ListFreeModelRec-uniq :
    (B : T.Model ℓB)
    (h : T.Homo (T.Model→Algebra ListFreeModel) (T.Model→Algebra B))
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
      ∙ cong (B .snd .fst unitOp) (funExt λ ())
    go (x ∷ xs) =
      sym
        (h .snd multOp
          (λ { false → ListFreeModelη x ; true → xs })
          (x ∷ xs) refl)
      ∙ cong (B .snd .fst multOp)
          (funExt λ { false → refl ; true → refl })
      ∙ cong (MonoidModelMult B (h .fst (ListFreeModelη x))) (go xs)

  ListFreeModelUniversal : (B : T.Model ℓB) →
    isEquiv
      (λ (h : T.Homo (T.Model→Algebra ListFreeModel) (T.Model→Algebra B)) x →
        h .fst (ListFreeModelη x))
  ListFreeModelUniversal B = isIsoToIsEquiv
    ( ListFreeModelRec B
    , (λ f → funExt (ListFreeModelRec-β B f))
    , (λ h → Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → B .fst .snd _ _)
        (sym (ListFreeModelRec-uniq B h)))
    )

-- An explicit characterization of the displayed free algebra
Listᴰ : (X : Type ℓX)(Xᴰ : X → Type ℓXᴰ) → List X → Type (ℓ-max ℓX ℓXᴰ)
Listᴰ X Xᴰ = ListP Xᴰ

module _ (X : Type ℓX)(Xᴰ : X → Type ℓXᴰ) where
  forget : List (Σ X Xᴰ) → List X
  forget = map fst

  ListFreeModelFiber : ∀ (xs : List X)
    → Iso (fiber forget xs)
          (Listᴰ X Xᴰ xs)
  ListFreeModelFiber xs =
    fiber forget xs
      Iso⟨ fiberMapIso fst xs ⟩
    ListP (fiber fst) xs
      Iso⟨ ListP-cong-Iso (λ x →
        fiber fst x
          Iso⟨ invIso (fiberProjIso _ Xᴰ _) ⟩
        Xᴰ x
          ∎Iso) xs ⟩
    Listᴰ X Xᴰ xs
      ∎Iso
