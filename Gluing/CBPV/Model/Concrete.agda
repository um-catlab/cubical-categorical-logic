-- Canonicity with concrete free models.
{-# OPTIONS --prop --lossy-unification #-}
module Gluing.CBPV.Model.Concrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Prop

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.Instances.Nat
open import Cubical.Algebra.Theory.Base
import Cubical.Algebra.Theory.Instances.Reader as Reader
import Cubical.Algebra.Theory.Instances.State as State
import Cubical.Algebra.Theory.Instances.Writer as Writer
import Cubical.Algebra.Theory.Instances.Monoid as FreeMonoid

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Displayed.Instances.Algebra.Model
import Gluing.CBPV.Model.Additive as Generic

private
  variable
    ℓR ℓS ℓW : Level

module ReaderBoolModelSyntax (Env : Type ℓR) where
  private
    T = Reader.ReaderTheory Env
  open Generic.BoolModelSyntax T public

  ReaderFreeBool≅ : CatIso (MODEL T ℓR) FreeBoolMODEL
    (Reader.ReaderFreeModel Env LiftBool)
  ReaderFreeBool≅ = FreeMODEL≅ T
    (Reader.ReaderFreeModel Env LiftBool)
    (Reader.ReaderFreeModelη Env LiftBool)
    (Reader.ReaderFreeModelUniversal Env LiftBool)

  ReaderCanonicity : Iso (Env → Lift ℓR Bool) (Tm tt UnitTy FBoolTy)
  ReaderCanonicity =
    CatIso→Iso (preserveIsosF {F = MODELForget T}
      (⋆Iso (invIso ReaderFreeBool≅) freeBool≅Syntax))

module WriterBoolModelSyntax (W : Monoid ℓW) where
  private
    T = Writer.WriterTheory W
  open Generic.BoolModelSyntax T public

  WriterFreeBool≅ : CatIso (MODEL T ℓW) FreeBoolMODEL
    (Writer.WriterFreeModel W LiftBool)
  WriterFreeBool≅ = FreeMODEL≅ T
    (Writer.WriterFreeModel W LiftBool)
    (Writer.WriterFreeModelη W LiftBool)
    (Writer.WriterFreeModelUniversal W LiftBool)

  WriterCanonicity : Iso (⟨ W ⟩ × Lift ℓW Bool) (Tm tt UnitTy FBoolTy)
  WriterCanonicity =
    CatIso→Iso (preserveIsosF {F = MODELForget T}
      (⋆Iso (invIso WriterFreeBool≅) freeBool≅Syntax))

module StateBoolModelSyntax (Store : hSet ℓS) where
  private
    T = State.StateTheory (Store .fst)
  open Generic.BoolModelSyntax T public

  StateFreeBool≅ : CatIso (MODEL T ℓS) FreeBoolMODEL
    (State.StateFreeModel Store LiftBool)
  StateFreeBool≅ = FreeMODEL≅ T
    (State.StateFreeModel Store LiftBool)
    (State.StateFreeModelη Store LiftBool)
    (State.StateFreeModelUniversal Store LiftBool)

  StateCanonicity :
    Iso (⟨ Store ⟩ → ⟨ Store ⟩ × Lift ℓS Bool) (Tm tt UnitTy FBoolTy)
  StateCanonicity =
    CatIso→Iso (preserveIsosF {F = MODELForget T}
      (⋆Iso (invIso StateFreeBool≅) freeBool≅Syntax))

module MonoidBoolModelSyntax where
  private
    T = FreeMonoid.MonoidTheory
  open Generic.BoolModelSyntax T public

  ListFreeBool≅ : CatIso (MODEL T ℓ-zero) FreeBoolMODEL
    (FreeMonoid.ListFreeModel LiftBool)
  ListFreeBool≅ = FreeMODEL≅ T
    (FreeMonoid.ListFreeModel LiftBool)
    (FreeMonoid.ListFreeModelη LiftBool)
    (FreeMonoid.ListFreeModelUniversal LiftBool)

  MonoidCanonicity : Iso (List (Lift ℓ-zero Bool)) (Tm tt UnitTy FBoolTy)
  MonoidCanonicity =
    CatIso→Iso (preserveIsosF {F = MODELForget T}
      (⋆Iso (invIso ListFreeBool≅) freeBool≅Syntax))

private
  module Examples where
    module _ where
      open StateBoolModelSyntax (Bool , isSetBool)
      open Theory (State.StateTheory Bool) using (var; app)

      _ : StateCanonicity .Iso.inv (seqS tru [ret]) ≡ λ s → s , lift true
      _ = refl

      _ : StateCanonicity .Iso.inv
        ([op] State.read λ s → if s then seqS fls [ret] else seqS tru [ret])
        true ≡ (true , lift false)
      _ = refl

      _ : StateCanonicity .Iso.inv
        ([op] (State.write true) λ _ → seqS fls [ret])
        ≡ λ _ → true , lift false
      _ = refl

      _ : unquote-FBool ([op] (State.write true) λ _ → seqS fls [ret])
        ≡ app (State.write true) λ _ → var (lift false)
      _ = refl

    module _ where
      open ReaderBoolModelSyntax Bool
      open Theory (Reader.ReaderTheory Bool) using (var; app)

      _ : ReaderCanonicity .Iso.inv (seqS tru [ret]) ≡ λ _ → lift true
      _ = refl

      _ : ReaderCanonicity .Iso.inv
        ([op] Reader.ask λ e → if e then seqS tru [ret] else seqS fls [ret])
        false ≡ lift false
      _ = refl

      _ : unquote-FBool ([op] Reader.ask λ _ → seqS tru [ret])
        ≡ app Reader.ask λ _ → var (lift true)
      _ = refl

    module _ where
      open WriterBoolModelSyntax NatMonoid
      open Theory (Writer.WriterTheory NatMonoid) using (var; app)

      _ : WriterCanonicity .Iso.inv (seqS tru [ret]) ≡ (0 , lift true)
      _ = refl

      _ : WriterCanonicity .Iso.inv
        ([op] (Writer.tell 2) λ _ → [op] (Writer.tell 3) λ _ → seqS fls [ret])
        ≡ (5 , lift false)
      _ = refl

      _ : unquote-FBool ([op] (Writer.tell 2) λ _ → seqS fls [ret])
        ≡ app (Writer.tell 2) λ _ → var (lift false)
      _ = refl

    module _ where
      open MonoidBoolModelSyntax
      open Theory FreeMonoid.MonoidTheory using (var; app)

      _ : MonoidCanonicity .Iso.inv (seqS tru [ret]) ≡ lift true ∷ []
      _ = refl

      _ : MonoidCanonicity .Iso.inv
        ([op] FreeMonoid.multOp λ b →
          if b then seqS tru [ret] else seqS fls [ret])
        ≡ lift false ∷ lift true ∷ []
      _ = refl

      _ : unquote-FBool ([op] FreeMonoid.multOp λ _ → seqS tru [ret])
        ≡ app FreeMonoid.multOp λ _ → var (lift true)
      _ = refl
