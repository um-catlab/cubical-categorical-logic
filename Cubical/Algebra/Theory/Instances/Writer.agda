-- The algebraic theory of a monoidal write-only output.
module Cubical.Algebra.Theory.Instances.Writer where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Monoid.Base
open import Cubical.Data.Sigma.More

open import Cubical.Algebra.Theory.Base

private
  variable
    ℓW ℓV ℓX ℓXᴰ ℓY ℓB ℓD ℓD' : Level

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
  WriterFreeModel .fst = (W .fst × X .fst) , isSet× W.is-set (X .snd)
  WriterFreeModel .snd .fst (tell w) γ =
    W._·_ w (γ tt .fst) , γ tt .snd
  WriterFreeModel .snd .snd tell-idEq ρ =
    ΣPathP (W.·IdL (ρ tt .fst) , refl)
  WriterFreeModel .snd .snd (tell-tellEq w w') ρ =
    ΣPathP (W.·Assoc w w' (ρ tt .fst) , refl)

  WriterFreeModelη : X .fst → ⟨ WriterFreeModel .fst ⟩
  WriterFreeModelη x = W.ε , x

  module _ (B : T.Model ℓB) (f : X .fst → ⟨ B .fst ⟩) where
    WriterFreeModelRec :
      T.Homo (T.Model→Algebra WriterFreeModel) (T.Model→Algebra B)
    WriterFreeModelRec .fst (w , x) =
      B .snd .fst (tell w) (λ _ → f x)
    WriterFreeModelRec .snd (tell w) γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      B .snd .snd (tell-tellEq w (γ tt .fst))
        (λ _ → f (γ tt .snd))
      ∙ cong (WriterFreeModelRec .fst) op∘γ≡op⟨γ⟩

    WriterFreeModelRec-β : (x : X .fst) →
      WriterFreeModelRec .fst (WriterFreeModelη x) ≡ f x
    WriterFreeModelRec-β x =
      B .snd .snd tell-idEq (λ _ → f x)

  WriterFreeModelRec-uniq :
    (B : T.Model ℓB)
    (f : T.Homo (T.Model→Algebra WriterFreeModel) (T.Model→Algebra B))
    → f .fst ≡
      WriterFreeModelRec B (λ x → f .fst (WriterFreeModelη x)) .fst
  WriterFreeModelRec-uniq B f = funExt λ { (w , x) →
    sym
      (f .snd (tell w) (λ _ → WriterFreeModelη x) (w , x)
        (ΣPathP (W.·IdR w , refl))) }

  WriterFreeModelUniversal : (B : T.Model ℓB) →
    isEquiv
      (λ (f : T.Homo (T.Model→Algebra WriterFreeModel) (T.Model→Algebra B)) x →
        f .fst (WriterFreeModelη x))
  WriterFreeModelUniversal B = isIsoToIsEquiv
    ( WriterFreeModelRec B
    , (λ f → funExt (WriterFreeModelRec-β B f))
    , (λ f → Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → B .fst .snd _ _)
        (sym (WriterFreeModelRec-uniq B f)))
    )

-- An explicit characterization of the displayed free algebra
module _ (W : Type ℓW) where
  Writer : Type ℓX → Type (ℓ-max ℓW ℓX)
  Writer X = W × X

  mapWriter : {X : Type ℓX}{Y : Type ℓY} → (X → Y) → Writer X → Writer Y
  mapWriter f m = m .fst , f (m .snd)

  Writerᴰ : (X : Type ℓX)(Xᴰ : X → Type ℓXᴰ) → Writer X → Type ℓXᴰ
  Writerᴰ X Xᴰ m = Xᴰ (m .snd)

  module _ (X : Type ℓX)(Xᴰ : X → Type ℓXᴰ) where
    forget : Writer (Σ X Xᴰ) → Writer X
    forget = mapWriter fst

    WriterFreeModelFiber : ∀ (m : Writer X)
      → Iso (fiber forget m)
            (Writerᴰ X Xᴰ m)
    WriterFreeModelFiber m =
      fiber forget m
        Iso⟨ invIso (fiber-map-idfun× fst _ _) ⟩
      fiber fst (m .snd)
        Iso⟨ invIso (fiberProjIso _ Xᴰ _) ⟩
      Writerᴰ X Xᴰ m
        ∎Iso
