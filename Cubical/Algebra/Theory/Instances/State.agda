-- The algebraic theory of a single mutable store.
module Cubical.Algebra.Theory.Instances.State where

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
    ℓS ℓV ℓX ℓB ℓD ℓD' : Level

data StateOp {ℓS : Level} (Store : Type ℓS) : Type ℓS where
  read : StateOp Store
  write : Store → StateOp Store

StateSignature : (Store : Type ℓS) → Signature ℓS ℓS
StateSignature Store .Signature.Op = StateOp Store
StateSignature Store .Signature.Arity read = Store
StateSignature Store .Signature.Arity (write _) = Unit*

module StateSignature {s : Level} (Store : Type s) where
  open Signature (StateSignature Store) public

module _ (Store : Type ℓS) where
  open Signature (StateSignature Store)

  readTm : ∀ {V : Type ℓV}
    → (Store → |FreeAlgebra| V) → |FreeAlgebra| V
  readTm γ = app read γ

  writeTm : ∀ {V : Type ℓV}
    → Store → |FreeAlgebra| V → |FreeAlgebra| V
  writeTm s t = app (write s) (λ _ → t)

  data StateEq : Type ℓS where
    wt-rdEq : Store → StateEq
    rd-wtEq : StateEq
    wt-wtEq : Store → Store → StateEq

  StateEqArity : StateEq → Type ℓS
  StateEqArity (wt-rdEq _) = Store
  StateEqArity rd-wtEq = Unit*
  StateEqArity (wt-wtEq _ _) = Unit*

  StateLhs : (e : StateEq) → |FreeAlgebra| (StateEqArity e)
  StateLhs (wt-rdEq s) =
    writeTm s (readTm var)
  StateLhs rd-wtEq = var tt*
  StateLhs (wt-wtEq s s') =
    writeTm s (writeTm s' (var tt*))

  StateRhs : (e : StateEq) → |FreeAlgebra| (StateEqArity e)
  StateRhs (wt-rdEq s) = writeTm s (var s)
  StateRhs rd-wtEq = readTm (λ s → writeTm s (var tt*))
  StateRhs (wt-wtEq _ s') = writeTm s' (var tt*)

  StateTheory : Theory ℓS ℓS ℓS ℓS
  StateTheory .Theory.S = StateSignature Store
  StateTheory .Theory.Eq = StateEq
  StateTheory .Theory.EqArity = StateEqArity
  StateTheory .Theory.lhs = StateLhs
  StateTheory .Theory.rhs = StateRhs

module StateTheory {s : Level} (Store : Type s) where
  open Theory (StateTheory Store) public

module _ (Store : Type ℓS) (B : Theory.Model (StateTheory Store) ℓB) where
  StateModelRead : (Store → B .fst .fst) → B .fst .fst
  StateModelRead γ = B .fst .snd read γ

  StateModelWrite : Store → B .fst .fst → B .fst .fst
  StateModelWrite s x = B .fst .snd (write s) (λ _ → x)

  StateModelWriteRead : (s : Store) (γ : Store → B .fst .fst) →
    StateModelWrite s (StateModelRead γ) ≡ StateModelWrite s (γ s)
  StateModelWriteRead s γ =
    B .snd .fst (wt-rdEq s) γ

  StateModelReadWrite : (x : B .fst .fst) →
    x ≡ StateModelRead (λ s → StateModelWrite s x)
  StateModelReadWrite x =
    B .snd .fst rd-wtEq (λ _ → x)

  StateModelWriteWrite : (s s' : Store) (x : B .fst .fst) →
    StateModelWrite s (StateModelWrite s' x) ≡ StateModelWrite s' x
  StateModelWriteWrite s s' x =
    B .snd .fst (wt-wtEq s s') (λ _ → x)

  StateModelReadRead : (γ : Store → Store → B .fst .fst) →
    StateModelRead (λ s → StateModelRead (γ s)) ≡
      StateModelRead (λ s → γ s s)
  StateModelReadRead γ =
    StateModelReadWrite (StateModelRead (λ s → StateModelRead (γ s)))
    ∙ cong StateModelRead
        (funExt λ s →
          StateModelWriteRead s (λ s' → StateModelRead (γ s'))
          ∙ StateModelWriteRead s (γ s)
          ∙ sym (StateModelWriteRead s (λ s' → γ s' s')))
    ∙ sym (StateModelReadWrite (StateModelRead (λ s → γ s s)))

  StateModelReadIdempotent : (x : B .fst .fst) →
    StateModelRead (λ _ → x) ≡ x
  StateModelReadIdempotent x =
    StateModelReadWrite (StateModelRead (λ _ → x))
    ∙ cong StateModelRead
        (funExt λ s → StateModelWriteRead s (λ _ → x))
    ∙ sym (StateModelReadWrite x)

module _ (Store : hSet ℓS) (X : hSet ℓX) where
  open Theory (StateTheory (Store .fst))

  StateFreeModel : Model (ℓ-max ℓS ℓX)
  StateFreeModel .fst .fst = Store .fst → Store .fst × X .fst
  StateFreeModel .fst .snd read γ s = γ s s
  StateFreeModel .fst .snd (write s) γ _ = γ tt* s
  StateFreeModel .snd .fst (wt-rdEq s) ρ =
    funExt λ _ → refl
  StateFreeModel .snd .fst rd-wtEq ρ =
    funExt λ _ → refl
  StateFreeModel .snd .fst (wt-wtEq s s') ρ =
    funExt λ _ → refl
  StateFreeModel .snd .snd =
    isSetΠ λ _ → isSet× (Store .snd) (X .snd)

  StateFreeModelη : X .fst → StateFreeModel .fst .fst
  StateFreeModelη x s = s , x

  module _ (B : Model ℓB) (f : X .fst → B .fst .fst) where
    StateFreeModelRec : Homo (StateFreeModel .fst) (B .fst)
    StateFreeModelRec .fst q =
      StateModelRead (Store .fst) B λ s →
        StateModelWrite (Store .fst) B (q s .fst) (f (q s .snd))
    StateFreeModelRec .snd read γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      StateModelReadRead (Store .fst) B
        (λ s s' →
          StateModelWrite (Store .fst) B
            (γ s s' .fst) (f (γ s s' .snd)))
      ∙ cong (StateFreeModelRec .fst) op∘γ≡op⟨γ⟩
    StateFreeModelRec .snd (write s) γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      StateModelWriteRead (Store .fst) B s
        (λ s' →
          StateModelWrite (Store .fst) B
            (γ tt* s' .fst) (f (γ tt* s' .snd)))
      ∙ StateModelWriteWrite (Store .fst) B s (γ tt* s .fst)
          (f (γ tt* s .snd))
      ∙ sym
          (StateModelReadIdempotent (Store .fst) B
            (StateModelWrite (Store .fst) B
              (γ tt* s .fst) (f (γ tt* s .snd))))
      ∙ cong (StateFreeModelRec .fst) op∘γ≡op⟨γ⟩

    StateFreeModelRec-β : (x : X .fst) →
      StateFreeModelRec .fst (StateFreeModelη x) ≡ f x
    StateFreeModelRec-β x =
      sym (StateModelReadWrite (Store .fst) B (f x))

  StateFreeModelRec-uniq :
    (B : Model ℓB)
    (f : Homo (StateFreeModel .fst) (B .fst))
    → f .fst ≡
      StateFreeModelRec B (λ x → f .fst (StateFreeModelη x)) .fst
  StateFreeModelRec-uniq B f = funExt λ q →
    sym
      ( cong (StateModelRead (Store .fst) B)
          (funExt λ s → f .snd (write _) _ _ refl)
      ∙ f .snd read _ _ refl)

  StateFreeModelUniversal : (B : Model ℓB) →
    isEquiv
      (λ (f : Homo (StateFreeModel .fst) (B .fst)) x →
        f .fst (StateFreeModelη x))
  StateFreeModelUniversal B = isIsoToIsEquiv
    ( StateFreeModelRec B
    , (λ f → funExt (StateFreeModelRec-β B f))
    , (λ f → Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → B .snd .snd _ _)
        (sym (StateFreeModelRec-uniq B f)))
    )

  module _ (Xᴰ : X .fst → hSet ℓD) where
    private
      module R = hSetReasoning
        (StateFreeModel .fst .fst , StateFreeModel .snd .snd)
        (λ q → (s : Store .fst) → Xᴰ (q s .snd) .fst)

    StateFreeAlgebraᴰ :
      Algebraᴰ (StateFreeModel .fst) (ℓ-max ℓS ℓD)
    StateFreeAlgebraᴰ .fst q =
      (s : Store .fst) → Xᴰ (q s .snd) .fst
    StateFreeAlgebraᴰ .snd read γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      R.reind op∘γ≡op⟨γ⟩ (λ s → γᴰ s s)
    StateFreeAlgebraᴰ .snd (write s) γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      R.reind op∘γ≡op⟨γ⟩ (λ _ → γᴰ tt* s)

    StateReadNormalize :
      (γ : Store .fst → StateFreeModel .fst .fst)
      (γᴰ : (s : Store .fst) → StateFreeAlgebraᴰ .fst (γ s))
      → Path (∫Algebra StateFreeAlgebraᴰ .fst)
          ( StateFreeModel .fst .snd read γ
          , StateFreeAlgebraᴰ .snd read γ γᴰ _ refl)
          ( StateFreeModel .fst .snd read γ
          , λ s → γᴰ s s)
    StateReadNormalize γ γᴰ = R.reind-filler⁻ refl

    StateWriteNormalize :
      (s : Store .fst)
      (γ : Unit* → StateFreeModel .fst .fst)
      (γᴰ : (u : Unit*) → StateFreeAlgebraᴰ .fst (γ u))
      → Path (∫Algebra StateFreeAlgebraᴰ .fst)
          ( StateFreeModel .fst .snd (write s) γ
          , StateFreeAlgebraᴰ .snd (write s) γ γᴰ _ refl)
          ( StateFreeModel .fst .snd (write s) γ
          , λ _ → γᴰ tt* s)
    StateWriteNormalize s γ γᴰ = R.reind-filler⁻ refl

    StateReadAppFiller : {V : Type ℓV}
      (ρ : V → StateFreeModel .fst .fst)
      (ρᴰ : (v : V) → StateFreeAlgebraᴰ .fst (ρ v))
      (γ : Store .fst → |FreeAlgebra| V)
      → Path (∫Algebra StateFreeAlgebraᴰ .fst)
          ( StateFreeModel .fst .snd read
              (λ s → interp (StateFreeModel .fst) ρ (γ s))
          , StateFreeAlgebraᴰ .snd read
              (λ s → interp (StateFreeModel .fst) ρ (γ s))
              (λ s → interpᴰ StateFreeAlgebraᴰ ρ ρᴰ (γ s))
              _ refl)
          ( interp (StateFreeModel .fst) ρ (app read γ)
          , interpᴰ StateFreeAlgebraᴰ ρ ρᴰ (app read γ))
    StateReadAppFiller ρ ρᴰ γ =
      Algebraᴰ-op-filler StateFreeAlgebraᴰ read
        (λ s → interp (StateFreeModel .fst) ρ (γ s))
        (λ s → interpᴰ StateFreeAlgebraᴰ ρ ρᴰ (γ s))
        (interp (StateFreeModel .fst) ρ (app read γ))
        (recFA (StateFreeModel .fst) ρ .snd read γ
          (app read γ) refl)

    StateWriteAppFiller : {V : Type ℓV}
      (s : Store .fst)
      (ρ : V → StateFreeModel .fst .fst)
      (ρᴰ : (v : V) → StateFreeAlgebraᴰ .fst (ρ v))
      (γ : Unit* → |FreeAlgebra| V)
      → Path (∫Algebra StateFreeAlgebraᴰ .fst)
          ( StateFreeModel .fst .snd (write s)
              (λ u → interp (StateFreeModel .fst) ρ (γ u))
          , StateFreeAlgebraᴰ .snd (write s)
              (λ u → interp (StateFreeModel .fst) ρ (γ u))
              (λ u → interpᴰ StateFreeAlgebraᴰ ρ ρᴰ (γ u))
              _ refl)
          ( interp (StateFreeModel .fst) ρ (app (write s) γ)
          , interpᴰ StateFreeAlgebraᴰ ρ ρᴰ
              (app (write s) γ))
    StateWriteAppFiller s ρ ρᴰ γ =
      Algebraᴰ-op-filler StateFreeAlgebraᴰ (write s)
        (λ u → interp (StateFreeModel .fst) ρ (γ u))
        (λ u → interpᴰ StateFreeAlgebraᴰ ρ ρᴰ (γ u))
        (interp (StateFreeModel .fst) ρ (app (write s) γ))
        (recFA (StateFreeModel .fst) ρ .snd (write s) γ
          (app (write s) γ) refl)

    StateFreeModelᴰ :
      Modelᴰ StateFreeModel (ℓ-max ℓS ℓD)
    StateFreeModelᴰ .fst = StateFreeAlgebraᴰ
    StateFreeModelᴰ .snd .fst (wt-rdEq s) ρ ρᴰ =
      R.rectifyOut {e' = StateFreeModel .snd .fst (wt-rdEq s) ρ}
        ( sym (StateWriteAppFiller s ρ ρᴰ
            (λ _ → app read var))
        ∙ StateWriteNormalize s
            (λ _ → interp (StateFreeModel .fst) ρ
              (app read var))
            (λ _ → interpᴰ StateFreeAlgebraᴰ ρ ρᴰ
              (app read var))
        ∙ cong writeTotal innerPath
        ∙ sym (StateWriteNormalize s
            (λ _ → ρ s) (λ _ → ρᴰ s))
        ∙ StateWriteAppFiller s ρ ρᴰ (λ _ → var s))
      where
      innerPath : Path (∫Algebra StateFreeAlgebraᴰ .fst)
        ( interp (StateFreeModel .fst) ρ (app read var)
        , interpᴰ StateFreeAlgebraᴰ ρ ρᴰ
            (app read var))
        ( StateFreeModel .fst .snd read ρ
        , λ s' → ρᴰ s' s')
      innerPath =
        sym (StateReadAppFiller ρ ρᴰ var)
        ∙ StateReadNormalize ρ ρᴰ

      writeTotal : ∫Algebra StateFreeAlgebraᴰ .fst →
        ∫Algebra StateFreeAlgebraᴰ .fst
      writeTotal z =
        (λ _ → z .fst s) , (λ _ → z .snd s)
    StateFreeModelᴰ .snd .fst rd-wtEq ρ ρᴰ =
      R.rectifyOut {e' = StateFreeModel .snd .fst rd-wtEq ρ}
        (sym rhsToLhs)
      where
      innerPath : (s : Store .fst) →
        Path (∫Algebra StateFreeAlgebraᴰ .fst)
          ( interp (StateFreeModel .fst) ρ
              (app (write s) (λ _ → var tt*))
          , interpᴰ StateFreeAlgebraᴰ ρ ρᴰ
              (app (write s) (λ _ → var tt*)))
          ( StateFreeModel .fst .snd (write s) (λ _ → ρ tt*)
          , λ _ → ρᴰ tt* s)
      innerPath s =
        sym (StateWriteAppFiller s ρ ρᴰ (λ _ → var tt*))
        ∙ StateWriteNormalize s (λ _ → ρ tt*) (λ _ → ρᴰ tt*)

      middlePath : Path (∫Algebra StateFreeAlgebraᴰ .fst)
        ( StateFreeModel .fst .snd read
            (λ s → interp (StateFreeModel .fst) ρ
              (app (write s) (λ _ → var tt*)))
        , λ s → interpᴰ StateFreeAlgebraᴰ ρ ρᴰ
            (app (write s) (λ _ → var tt*)) s)
        (ρ tt* , ρᴰ tt*)
      middlePath i .fst s = innerPath s i .fst s
      middlePath i .snd s = innerPath s i .snd s

      rhsToLhs : Path (∫Algebra StateFreeAlgebraᴰ .fst)
        ( interp (StateFreeModel .fst) ρ
            (app read
              (λ s → app (write s) (λ _ → var tt*)))
        , interpᴰ StateFreeAlgebraᴰ ρ ρᴰ
            (app read
              (λ s → app (write s) (λ _ → var tt*))))
        (ρ tt* , ρᴰ tt*)
      rhsToLhs =
        sym (StateReadAppFiller ρ ρᴰ
          (λ s → app (write s) (λ _ → var tt*)))
        ∙ StateReadNormalize
            (λ s → interp (StateFreeModel .fst) ρ
              (app (write s) (λ _ → var tt*)))
            (λ s → interpᴰ StateFreeAlgebraᴰ ρ ρᴰ
              (app (write s) (λ _ → var tt*)))
        ∙ middlePath
    StateFreeModelᴰ .snd .fst (wt-wtEq s s') ρ ρᴰ =
      R.rectifyOut {e' = StateFreeModel .snd .fst (wt-wtEq s s') ρ}
        ( sym (StateWriteAppFiller s ρ ρᴰ
            (λ _ → app (write s') (λ _ → var tt*)))
        ∙ StateWriteNormalize s
            (λ _ → interp (StateFreeModel .fst) ρ
              (app (write s') (λ _ → var tt*)))
            (λ _ → interpᴰ StateFreeAlgebraᴰ ρ ρᴰ
              (app (write s') (λ _ → var tt*)))
        ∙ cong writeTotal innerPath
        ∙ sym (StateWriteNormalize s'
            (λ _ → ρ tt*) (λ _ → ρᴰ tt*))
        ∙ StateWriteAppFiller s' ρ ρᴰ (λ _ → var tt*))
      where
      innerPath : Path (∫Algebra StateFreeAlgebraᴰ .fst)
        ( interp (StateFreeModel .fst) ρ
            (app (write s') (λ _ → var tt*))
        , interpᴰ StateFreeAlgebraᴰ ρ ρᴰ
            (app (write s') (λ _ → var tt*)))
        ( StateFreeModel .fst .snd (write s') (λ _ → ρ tt*)
        , λ _ → ρᴰ tt* s')
      innerPath =
        sym (StateWriteAppFiller s' ρ ρᴰ (λ _ → var tt*))
        ∙ StateWriteNormalize s' (λ _ → ρ tt*) (λ _ → ρᴰ tt*)

      writeTotal : ∫Algebra StateFreeAlgebraᴰ .fst →
        ∫Algebra StateFreeAlgebraᴰ .fst
      writeTotal z =
        (λ _ → z .fst s) , (λ _ → z .snd s)
    StateFreeModelᴰ .snd .snd q =
      isSetΠ λ s → Xᴰ (q s .snd) .snd

    StateFreeModelηᴰ : (x : X .fst) → Xᴰ x .fst →
      StateFreeModelᴰ .fst .fst (StateFreeModelη x)
    StateFreeModelηᴰ x xᴰ _ = xᴰ

    module _
      (Bᴰ : Modelᴰ StateFreeModel ℓD')
      (fᴰ : (x : X .fst) → Xᴰ x .fst →
        Bᴰ .fst .fst (StateFreeModelη x))
      where
      private
        TargetModel : Model (ℓ-max (ℓ-max ℓS ℓX) ℓD')
        TargetModel = ∫Model {M = StateFreeModel} Bᴰ

        module BᴰR = hSetReasoning
          (StateFreeModel .fst .fst , StateFreeModel .snd .snd)
          (Bᴰ .fst .fst)

        generator : (x : X .fst) (xᴰ : Xᴰ x .fst) →
          TargetModel .fst .fst
        generator x xᴰ = StateFreeModelη x , fᴰ x xᴰ

        RecᴰTotal : ∫Algebra StateFreeAlgebraᴰ .fst →
          TargetModel .fst .fst
        RecᴰTotal z =
          StateModelRead (Store .fst) TargetModel λ s →
            StateModelWrite (Store .fst) TargetModel (z .fst s .fst)
              (generator (z .fst s .snd) (z .snd s))

      StateFreeModelRecᴰ-fun :
        (q : StateFreeModel .fst .fst) →
        StateFreeAlgebraᴰ .fst q → Bᴰ .fst .fst q
      StateFreeModelRecᴰ-fun q qᴰ = RecᴰTotal (q , qᴰ) .snd

      StateFreeModelRecᴰ-β : (x : X .fst) (xᴰ : Xᴰ x .fst) →
        StateFreeModelRecᴰ-fun
          (StateFreeModelη x) (StateFreeModelηᴰ x xᴰ) ≡ fᴰ x xᴰ
      StateFreeModelRecᴰ-β x xᴰ = BᴰR.rectifyOut {e' = refl}
        (sym (StateModelReadWrite (Store .fst) TargetModel
          (generator x xᴰ)))

      StateFreeModelRecᴰ :
        Homoᴰ (idHomo {A = StateFreeModel .fst})
          StateFreeAlgebraᴰ (Bᴰ .fst)
      StateFreeModelRecᴰ .fst = StateFreeModelRecᴰ-fun
      StateFreeModelRecᴰ .snd read γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
        op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
          BᴰR.rectifyOut {e' = refl}
            ( sym (Algebraᴰ-op-filler (Bᴰ .fst) read γ
                (λ s → StateFreeModelRecᴰ-fun (γ s) (γᴰ s))
                op⟨γ⟩ op∘γ≡op⟨γ⟩)
            ∙ StateModelReadRead (Store .fst) TargetModel matrix
            ∙ cong RecᴰTotal sourcePath)
          where
          matrix : Store .fst → Store .fst → TargetModel .fst .fst
          matrix s s' =
            StateModelWrite (Store .fst) TargetModel (γ s s' .fst)
              (generator (γ s s' .snd) (γᴰ s s'))

          sourcePath : Path (∫Algebra StateFreeAlgebraᴰ .fst)
            ( StateFreeModel .fst .snd read γ
            , λ s → γᴰ s s)
            (op⟨γ⟩ , op⟨γᴰ⟩)
          sourcePath =
            R.reind-filler op∘γ≡op⟨γ⟩
            ∙ R.≡in {pth = refl} op∘γᴰ≡op⟨γᴰ⟩
      StateFreeModelRecᴰ .snd (write s) γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
        op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
          BᴰR.rectifyOut {e' = refl}
            ( sym (Algebraᴰ-op-filler (Bᴰ .fst) (write s) γ
                (λ u → StateFreeModelRecᴰ-fun (γ u) (γᴰ u))
                op⟨γ⟩ op∘γ≡op⟨γ⟩)
            ∙ StateModelWriteRead (Store .fst) TargetModel s matrix
            ∙ StateModelWriteWrite (Store .fst) TargetModel s output
                (generator value valueᴰ)
            ∙ sym (StateModelReadIdempotent (Store .fst) TargetModel
                (StateModelWrite (Store .fst) TargetModel output
                  (generator value valueᴰ)))
            ∙ cong RecᴰTotal sourcePath)
          where
          matrix : Store .fst → TargetModel .fst .fst
          matrix s' =
            StateModelWrite (Store .fst) TargetModel
              (γ tt* s' .fst)
              (generator (γ tt* s' .snd) (γᴰ tt* s'))

          output : Store .fst
          output = γ tt* s .fst

          value : X .fst
          value = γ tt* s .snd

          valueᴰ : Xᴰ value .fst
          valueᴰ = γᴰ tt* s

          sourcePath : Path (∫Algebra StateFreeAlgebraᴰ .fst)
            ( StateFreeModel .fst .snd (write s) γ
            , λ _ → γᴰ tt* s)
            (op⟨γ⟩ , op⟨γᴰ⟩)
          sourcePath =
            R.reind-filler op∘γ≡op⟨γ⟩
            ∙ R.≡in {pth = refl} op∘γᴰ≡op⟨γᴰ⟩

    StateFreeModelRecᴰ-uniq :
      (Bᴰ : Modelᴰ StateFreeModel ℓD')
      (hᴰ : Homoᴰ (idHomo {A = StateFreeModel .fst})
        StateFreeAlgebraᴰ (Bᴰ .fst))
      → hᴰ .fst ≡
        StateFreeModelRecᴰ Bᴰ
          (λ x xᴰ → hᴰ .fst
            (StateFreeModelη x) (StateFreeModelηᴰ x xᴰ)) .fst
    StateFreeModelRecᴰ-uniq Bᴰ hᴰ =
      funExt λ q → funExt λ qᴰ →
        BᴰR.rectifyOut {e' = refl} (sym (totalPath q qᴰ))
      where
      TargetModel : Model _
      TargetModel = ∫Model {M = StateFreeModel} Bᴰ

      module BᴰR = hSetReasoning
        (StateFreeModel .fst .fst , StateFreeModel .snd .snd)
        (Bᴰ .fst .fst)

      HomoᴰTotal : Homo
        (∫Algebra StateFreeAlgebraᴰ)
        (TargetModel .fst)
      HomoᴰTotal .fst z = z .fst , hᴰ .fst (z .fst) (z .snd)
      HomoᴰTotal .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
        Algebraᴰ-op-filler (Bᴰ .fst) op
          (λ v → γ v .fst)
          (λ v → hᴰ .fst (γ v .fst) (γ v .snd))
          (op⟨γ⟩ .fst) basePath
        ∙ BᴰR.≡in {pth = refl}
            (hᴰ .snd op
              (λ v → γ v .fst) (λ v → γ v .snd)
              (op⟨γ⟩ .fst) basePath (op⟨γ⟩ .snd) sourceᴰ≡)
        where
        basePath : StateFreeModel .fst .snd op (λ v → γ v .fst) ≡
          op⟨γ⟩ .fst
        basePath i = op∘γ≡op⟨γ⟩ i .fst

        sourceᴰ≡ :
          StateFreeAlgebraᴰ .snd op
            (λ v → γ v .fst) (λ v → γ v .snd)
            (op⟨γ⟩ .fst) basePath
          ≡ op⟨γ⟩ .snd
        sourceᴰ≡ = R.rectifyOut {e' = refl}
          ( sym (Algebraᴰ-op-filler StateFreeAlgebraᴰ op
              (λ v → γ v .fst) (λ v → γ v .snd)
              (op⟨γ⟩ .fst) basePath)
          ∙ op∘γ≡op⟨γ⟩)

      generator : (x : X .fst) (xᴰ : Xᴰ x .fst) →
        ∫Algebra StateFreeAlgebraᴰ .fst
      generator x xᴰ = StateFreeModelη x , StateFreeModelηᴰ x xᴰ

      branch : (q : StateFreeModel .fst .fst)
        (qᴰ : StateFreeAlgebraᴰ .fst q) (s : Store .fst) →
        ∫Algebra StateFreeAlgebraᴰ .fst
      branch q qᴰ s =
        ∫Algebra StateFreeAlgebraᴰ .snd (write (q s .fst))
          (λ _ → generator (q s .snd) (qᴰ s))

      branchNormalize : (q : StateFreeModel .fst .fst)
        (qᴰ : StateFreeAlgebraᴰ .fst q) (s : Store .fst) →
        Path (∫Algebra StateFreeAlgebraᴰ .fst)
          (branch q qᴰ s)
          ((λ _ → q s) , (λ _ → qᴰ s))
      branchNormalize q qᴰ s =
        StateWriteNormalize (q s .fst)
          (λ _ → StateFreeModelη (q s .snd))
          (λ _ → StateFreeModelηᴰ (q s .snd) (qᴰ s))

      representationPath : (q : StateFreeModel .fst .fst)
        (qᴰ : StateFreeAlgebraᴰ .fst q) →
        Path (∫Algebra StateFreeAlgebraᴰ .fst)
          (∫Algebra StateFreeAlgebraᴰ .snd read (branch q qᴰ))
          (q , qᴰ)
      representationPath q qᴰ =
        cong (∫Algebra StateFreeAlgebraᴰ .snd read)
          (funExt (branchNormalize q qᴰ))
        ∙ StateReadNormalize (λ s → λ _ → q s) (λ s → λ _ → qᴰ s)

      branchHomoPath : (q : StateFreeModel .fst .fst)
        (qᴰ : StateFreeAlgebraᴰ .fst q) (s : Store .fst) →
        Path (TargetModel .fst .fst)
          ( StateModelWrite (Store .fst) TargetModel (q s .fst)
              (HomoᴰTotal .fst (generator (q s .snd) (qᴰ s))) )
          (HomoᴰTotal .fst (branch q qᴰ s))
      branchHomoPath q qᴰ s =
        HomoᴰTotal .snd (write (q s .fst))
          (λ _ → generator (q s .snd) (qᴰ s))
          (branch q qᴰ s) refl

      totalPath : (q : StateFreeModel .fst .fst)
        (qᴰ : StateFreeAlgebraᴰ .fst q) →
        Path (TargetModel .fst .fst)
          ( q
          , StateFreeModelRecᴰ Bᴰ
              (λ x xᴰ → hᴰ .fst
                (StateFreeModelη x) (StateFreeModelηᴰ x xᴰ))
              .fst q qᴰ)
          (q , hᴰ .fst q qᴰ)
      totalPath q qᴰ =
        cong (StateModelRead (Store .fst) TargetModel)
          (funExt (branchHomoPath q qᴰ))
        ∙ HomoᴰTotal .snd read (branch q qᴰ) (q , qᴰ)
            (representationPath q qᴰ)

    StateFreeModelUniversalᴰ :
      (Bᴰ : Modelᴰ StateFreeModel ℓD') →
      isEquiv
        (λ (hᴰ : Homoᴰ (idHomo {A = StateFreeModel .fst})
            StateFreeAlgebraᴰ (Bᴰ .fst)) x xᴰ →
          hᴰ .fst (StateFreeModelη x) (StateFreeModelηᴰ x xᴰ))
    StateFreeModelUniversalᴰ Bᴰ = isIsoToIsEquiv
      ( StateFreeModelRecᴰ Bᴰ
      , (λ fᴰ → funExt λ x → funExt λ xᴰ →
          StateFreeModelRecᴰ-β Bᴰ fᴰ x xᴰ)
      , (λ hᴰ → Σ≡Prop
          (λ _ → isPropΠ6 λ _ _ _ _ _ _ →
            isPropΠ λ _ → Bᴰ .snd .snd _ _ _)
          (sym (StateFreeModelRecᴰ-uniq Bᴰ hᴰ)))
      )

    module _ {B : Model ℓB}
      (ϕ : Homo (StateFreeModel .fst) (B .fst))
      (Bᴰ : Modelᴰ B ℓD')
      (fᴰ : (x : X .fst) → Xᴰ x .fst →
        Bᴰ .fst .fst (ϕ .fst (StateFreeModelη x)))
      where
      StateFreeModelRecOverᴰ :
        Homoᴰ ϕ StateFreeAlgebraᴰ (Bᴰ .fst)
      StateFreeModelRecOverᴰ =
        StateFreeModelRecᴰ
          (_*_ {M = StateFreeModel} {N = B} ϕ Bᴰ) fᴰ

      StateFreeModelRecOverᴰ-β :
        (x : X .fst) (xᴰ : Xᴰ x .fst) →
        StateFreeModelRecOverᴰ .fst
          (StateFreeModelη x) (StateFreeModelηᴰ x xᴰ) ≡ fᴰ x xᴰ
      StateFreeModelRecOverᴰ-β =
        StateFreeModelRecᴰ-β
          (_*_ {M = StateFreeModel} {N = B} ϕ Bᴰ) fᴰ

    StateFreeModelRecOverᴰ-uniq : {B : Model ℓB}
      (ϕ : Homo (StateFreeModel .fst) (B .fst))
      (Bᴰ : Modelᴰ B ℓD')
      (hᴰ : Homoᴰ ϕ StateFreeAlgebraᴰ (Bᴰ .fst))
      → hᴰ .fst ≡ StateFreeModelRecOverᴰ {B = B} ϕ Bᴰ
          (λ x xᴰ → hᴰ .fst
            (StateFreeModelη x) (StateFreeModelηᴰ x xᴰ)) .fst
    StateFreeModelRecOverᴰ-uniq {B = B} ϕ Bᴰ =
      StateFreeModelRecᴰ-uniq
        (_*_ {M = StateFreeModel} {N = B} ϕ Bᴰ)

    StateFreeModelUniversalOverᴰ : {B : Model ℓB}
      (ϕ : Homo (StateFreeModel .fst) (B .fst))
      (Bᴰ : Modelᴰ B ℓD') →
      isEquiv
        (λ (hᴰ : Homoᴰ ϕ StateFreeAlgebraᴰ (Bᴰ .fst)) x xᴰ →
          hᴰ .fst (StateFreeModelη x) (StateFreeModelηᴰ x xᴰ))
    StateFreeModelUniversalOverᴰ {B = B} ϕ Bᴰ =
      StateFreeModelUniversalᴰ
        (_*_ {M = StateFreeModel} {N = B} ϕ Bᴰ)
