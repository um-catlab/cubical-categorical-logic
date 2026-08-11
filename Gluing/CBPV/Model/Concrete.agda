{-# OPTIONS --prop --lossy-unification #-}
module Gluing.CBPV.Model.Concrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool

open import Cubical.Algebra.Monoid.Base
import Cubical.Algebra.Theory.Instances.Reader as Reader
import Cubical.Algebra.Theory.Instances.State as State
import Cubical.Algebra.Theory.Instances.Writer as Writer

open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Multiplicative
import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.ConcreteFree as Concrete
import Gluing.CBPV.Model.Additive as Generic

private
  variable
    ℓR ℓS ℓW : Level

ReaderFreeMODELConstruction : (Env : Type ℓR) →
  FreeMODELConstruction (Reader.ReaderTheory Env)
ReaderFreeMODELConstruction Env =
  Concrete.ConcreteFreeMODELConstruction
    (Reader.ReaderTheory Env)
    (λ A → Reader.ReaderFreeModel Env A)
    (λ A → Reader.ReaderFreeModelη Env A)
    (λ A B → Reader.ReaderFreeModelUniversal Env A B)
    (λ A Aᴰ → Reader.ReaderFreeModelᴰ Env A Aᴰ)
    (λ A Aᴰ → Reader.ReaderFreeModelηᴰ Env A Aᴰ)
    (λ A Aᴰ {B} ϕ Bᴰ →
      Reader.ReaderFreeModelUniversalOverᴰ Env A Aᴰ ϕ Bᴰ)

ReaderBoolFreeMODELConstruction : (Env : Type ℓR) →
  BoolFreeMODELConstruction (Reader.ReaderTheory Env)
ReaderBoolFreeMODELConstruction Env .fst =
  Concrete.Model→MODEL (Reader.ReaderTheory Env)
    (Reader.ReaderFreeModel Env (Bool , isSetBool))
ReaderBoolFreeMODELConstruction Env .snd .fst =
  Reader.ReaderFreeModelη Env (Bool , isSetBool)
ReaderBoolFreeMODELConstruction Env .snd .snd B =
  Reader.ReaderFreeModelUniversal Env (Bool , isSetBool)
    (Concrete.MODEL→Model (Reader.ReaderTheory Env) B)

module ReaderBoolModelSyntax {ℓR : Level} (Env : Type ℓR) =
  Generic.BoolModelSyntaxWithFree
    (Reader.ReaderTheory Env)
    (ReaderFreeMODELConstruction Env)
    (ReaderBoolFreeMODELConstruction Env)

WriterFreeMODELConstruction : (W : Monoid ℓW) →
  FreeMODELConstruction (Writer.WriterTheory W)
WriterFreeMODELConstruction W =
  Concrete.ConcreteFreeMODELConstruction
    (Writer.WriterTheory W)
    (λ A → Writer.WriterFreeModel W A)
    (λ A → Writer.WriterFreeModelη W A)
    (λ A B → Writer.WriterFreeModelUniversal W A B)
    (λ A Aᴰ → Writer.WriterFreeModelᴰ W A Aᴰ)
    (λ A Aᴰ → Writer.WriterFreeModelηᴰ W A Aᴰ)
    (λ A Aᴰ {B} ϕ Bᴰ →
      Writer.WriterFreeModelUniversalOverᴰ W A Aᴰ ϕ Bᴰ)

WriterBoolFreeMODELConstruction : (W : Monoid ℓW) →
  BoolFreeMODELConstruction (Writer.WriterTheory W)
WriterBoolFreeMODELConstruction W .fst =
  Concrete.Model→MODEL (Writer.WriterTheory W)
    (Writer.WriterFreeModel W (Bool , isSetBool))
WriterBoolFreeMODELConstruction W .snd .fst =
  Writer.WriterFreeModelη W (Bool , isSetBool)
WriterBoolFreeMODELConstruction W .snd .snd B =
  Writer.WriterFreeModelUniversal W (Bool , isSetBool)
    (Concrete.MODEL→Model (Writer.WriterTheory W) B)

module WriterBoolModelSyntax {ℓW : Level} (W : Monoid ℓW) =
  Generic.BoolModelSyntaxWithFree
    (Writer.WriterTheory W)
    (WriterFreeMODELConstruction W)
    (WriterBoolFreeMODELConstruction W)

StateFreeMODELConstruction : (Store : hSet ℓS) →
  FreeMODELConstruction (State.StateTheory (Store .fst))
StateFreeMODELConstruction Store =
  Concrete.ConcreteFreeMODELConstruction
    (State.StateTheory (Store .fst))
    (λ A → State.StateFreeModel Store A)
    (λ A → State.StateFreeModelη Store A)
    (λ A B → State.StateFreeModelUniversal Store A B)
    (λ A Aᴰ → State.StateFreeModelᴰ Store A Aᴰ)
    (λ A Aᴰ → State.StateFreeModelηᴰ Store A Aᴰ)
    (λ A Aᴰ {B} ϕ Bᴰ →
      State.StateFreeModelUniversalOverᴰ Store A Aᴰ ϕ Bᴰ)

StateBoolFreeMODELConstruction : (Store : hSet ℓS) →
  BoolFreeMODELConstruction (State.StateTheory (Store .fst))
StateBoolFreeMODELConstruction Store .fst =
  Concrete.Model→MODEL (State.StateTheory (Store .fst))
    (State.StateFreeModel Store (Bool , isSetBool))
StateBoolFreeMODELConstruction Store .snd .fst =
  State.StateFreeModelη Store (Bool , isSetBool)
StateBoolFreeMODELConstruction Store .snd .snd B =
  State.StateFreeModelUniversal Store (Bool , isSetBool)
    (Concrete.MODEL→Model (State.StateTheory (Store .fst)) B)

module StateBoolModelSyntax {ℓS : Level} (Store : hSet ℓS) =
  Generic.BoolModelSyntaxWithFree
    (State.StateTheory (Store .fst))
    (StateFreeMODELConstruction Store)
    (StateBoolFreeMODELConstruction Store)
