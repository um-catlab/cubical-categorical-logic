{-# OPTIONS --lossy-unification #-}
module Gluing.BiCartesianClosedCategory.NatCanonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum.Properties
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.BiCartesianClosed.Base
open import Cubical.Categories.Displayed.Constructions.Weaken.UncurriedProperties
open import Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Forded as FreeBiCCC
  renaming ([_,_] to [_,+_])
open import Cubical.Categories.Constructions.Free.BiCartesianClosedCategory.Quiver

open import Gluing.BiCartesianClosedCategory.Canonicity

open Category
open Functor

module _ where
  data OB : Type where
    nat : OB

  data MOR : Type ℓ-zero where
    ze su : MOR

  open QuiverOver

  +×⇒QUIVER : +×⇒Quiver ℓ-zero ℓ-zero
  +×⇒QUIVER .+×⇒Quiver.ob = OB
  +×⇒QUIVER .+×⇒Quiver.Q .mor = MOR
  +×⇒QUIVER .+×⇒Quiver.Q .dom ze = ⊤
  +×⇒QUIVER .+×⇒Quiver.Q .dom su = ↑ nat
  +×⇒QUIVER .+×⇒Quiver.Q .cod ze = ↑ nat
  +×⇒QUIVER .+×⇒Quiver.Q .cod su = ↑ nat

  private
    module FREEBICCC = BiCartesianClosedCategory (FREE +×⇒QUIVER)

  [nat] : Type _
  [nat] = FREEBICCC.Hom[ ⊤ , ↑ nat ]

  [ze] : [nat]
  [ze] = ↑ₑ +×⇒QUIVER ze

  [su] : FREEBICCC.Hom[ ↑ nat , ↑ nat ]
  [su] = ↑ₑ +×⇒QUIVER su

  ＂_＂ : ℕ → [nat]
  ＂ zero ＂ = [ze]
  ＂ suc n ＂ = ＂ n ＂ ⋆ₑ [su]

  CanonicalFormNat : [nat] → hSet ℓ-zero
  CanonicalFormNat e =
    fiber ＂_＂ e ,
    isSetΣ isSetℕ (λ _ → isProp→isSet (FREEBICCC.isSetHom _ _))

  canonicalize-nat : ∀ (e : [nat]) → ⟨ CanonicalFormNat e ⟩
  canonicalize-nat = canonicalize +×⇒QUIVER
    (mkElimInterpᴰ
      (λ {nat e → CanonicalFormNat e})
      λ { ze e _ → 0 , (sym (cong₂ _⋆ₑ_ (⊤→⊤IsId +×⇒QUIVER e) refl ∙ FREEBICCC.⋆IdL _))
        ; su e (n , fib) → (suc n) , cong₂ _⋆ₑ_ fib refl
        })

  ⟦-⟧SET : Functor FREEBICCC.C (SET ℓ-zero)
  ⟦-⟧SET = FreeBiCCC.rec +×⇒QUIVER SETBiCCC (mkElimInterpᴰ
    (λ {nat → ℕ , isSetℕ})
    λ {ze → λ _ → 0 ; su → suc})

  evalNat : [nat] → ℕ
  evalNat e = ⟦-⟧SET .F-hom e tt*

  evalNat-＂_＂ : ∀ n → evalNat ＂ n ＂ ≡ n
  evalNat-＂_＂ zero = refl
  evalNat-＂_＂ (suc n) = cong suc (evalNat-＂_＂ n)

  ＂_＂-inj : ∀ {m n} → ＂ m ＂ ≡ ＂ n ＂ → m ≡ n
  ＂_＂-inj {m} {n} p = sym (evalNat-＂_＂ m) ∙ cong evalNat p ∙ evalNat-＂_＂ n

  canonicity : Iso [nat] ℕ
  canonicity .Iso.fun [n] = evalNat [n]
  canonicity .Iso.inv n = ＂ n ＂
  canonicity .Iso.sec n = evalNat-＂ n ＂
  canonicity .Iso.ret [n] =
    cong ＂_＂ (cong evalNat (sym p) ∙ evalNat-＂ m ＂) ∙ p
    where
    m = canonicalize-nat [n] .fst
    p = canonicalize-nat [n] .snd
