module Gluing.Canonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Limits.Cartesian.More public

open Category
open Section

private
  variable ℓC ℓC' ℓS : Level

module _
  {C : Category ℓC ℓC'}
  (base : C .ob)
  (S : Section (C [ base ,-]) (SETᴰ ℓC' ℓS))
  (seed : ⟨ S .F-obᴰ base (C .id) ⟩)
  where

  canonicalize : ∀ {o} (e : C [ base , o ]) → ⟨ S .F-obᴰ o e ⟩
  canonicalize e = subst (λ e → ⟨ S .F-obᴰ _ e ⟩) (C .⋆IdL e) (S .F-homᴰ e (C .id) seed)

module _
  {C : Category ℓC ℓC'}
  (term : Terminal' C)
  where
  open TerminalNotation term

  ⊤→⊤IsId : ∀ (e : C [ 𝟙 , 𝟙 ]) → e ≡ C .id
  ⊤→⊤IsId _ = 𝟙extensionality

module CanonicalFormIso
  {ℓ ℓ'} {[A] : Type ℓ} {A : Type ℓ'}
  (⌈_⌉ : A → [A])
  (eval : [A] → A)
  (sec : ∀ a → eval ⌈ a ⌉ ≡ a)
  (surj : ∀ e → fiber ⌈_⌉ e)
  where

  canonicity : Iso [A] A
  canonicity = section+surjection→Iso eval ⌈_⌉ sec surj

module BoolIso
  {ℓ} {[bool] : Type ℓ}
  ([t] [f] : [bool])
  (eval : [bool] → Bool)
  (eval-t : eval [t] ≡ true)
  (eval-f : eval [f] ≡ false)
  (canonicalize-bool : ∀ e → (e ≡ [t]) ⊎ (e ≡ [f]))
  where

  private
    fromBool : Bool → [bool]
    fromBool true = [t]
    fromBool false = [f]

  canonicity-bool : Iso [bool] Bool
  canonicity-bool = CanonicalFormIso.canonicity fromBool eval
    (λ { true → eval-t ; false → eval-f })
    (λ e → Sum.elim {C = λ _ → fiber fromBool e}
      (λ p → true , sym p) (λ q → false , sym q)
      (canonicalize-bool e))

module NatIso
  {ℓ} {[nat] : Type ℓ}
  (numeral : ℕ → [nat])
  (eval : [nat] → ℕ)
  (eval-numeral : ∀ n → eval (numeral n) ≡ n)
  (canonicalize-nat : ∀ e → fiber numeral e)
  where

  canonicity-nat : Iso [nat] ℕ
  canonicity-nat =
    CanonicalFormIso.canonicity numeral eval eval-numeral canonicalize-nat
