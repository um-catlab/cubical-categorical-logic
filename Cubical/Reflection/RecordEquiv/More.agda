{-
Adds the workaround for implicit arguments present in declareRecordIsoΣ
from here: https://github.com/agda/cubical/issues/995
Solution by @cmcmA20
-}
{-# OPTIONS --no-exact-split --safe #-}
module Cubical.Reflection.RecordEquiv.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.List as List
open import Cubical.Data.Nat
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Sigma

open import Agda.Builtin.String
import Agda.Builtin.Reflection as R
open import Cubical.Reflection.Base

open import Cubical.Reflection.RecordEquiv


defineRecordIsoΣ' : R.Name → ΣFormat → R.Name → R.TC Unit
defineRecordIsoΣ' idName σ recordName =
  recordName→isoTy recordName σ >>= λ isoTy →
  R.defineFun idName (recordIsoΣClauses σ)

defineRecordIsoΣ : R.Name → R.Name → R.TC Unit
defineRecordIsoΣ idName recordName =
  R.getDefinition recordName >>= λ where
  (R.record-type _ fs) →
    let σ = List→ΣFormat (List.map (λ {(R.arg _ n) → n}) fs) in
    defineRecordIsoΣ' idName σ recordName
  _ →
    R.typeError (R.strErr "Not a record type name:" ∷ R.nameErr recordName ∷ [])

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------
module _ where private
  Bar : Type
  Bar = ℕ

  private variable Z : Bar

  Baz : Bar → Type
  Baz 0 = Unit
  Baz _ = ℕ

  record Foo : Type where
    field
      foo : Baz Z

  foo-iso : Iso Foo (∀{A} → Baz A)
  unquoteDef foo-iso = defineRecordIsoΣ foo-iso (quote Foo)

module _ where private
  Bar : ℕ → Type
  Bar 0 = Unit
  Bar _ = ℕ

  record Foo {n : ℕ} (b : Bar n) : Type where
    field
      foo : {a : ℕ} → Bar a
      baz : Bar n
      goo : b ≡ baz

  Sigma : {n : ℕ} (b : Bar n) → Type
  Sigma {n} b = Σ ({a : ℕ} → Bar a) (λ z → Σ (Bar n) (PathP (λ i → Bar n) b))

  foo-iso : ∀ {x : ℕ} {b : Bar x} → Iso (Foo b) (Sigma b)
  unquoteDef foo-iso = defineRecordIsoΣ foo-iso (quote Foo)

