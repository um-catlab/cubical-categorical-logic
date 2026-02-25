module Gluing.Canonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base

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

module _
  (CC : CartesianCategory ℓC ℓC')
  (base : CC .CartesianCategory.C .ob)
  where
  open CartesianCategory CC

  PtsCartesian : CartesianFunctor CC (SET ℓC')
  PtsCartesian .fst = C [ base ,-]
  PtsCartesian .snd c c' X = isIsoToIsEquiv
    ((λ (f , g) x → f x ,p g x)
    , (λ _ → ΣPathP ((funExt λ _ → ×β₁) , (funExt λ _ → ×β₂)))
    , λ _ → funExt λ _ → ,p≡ refl refl)

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
  canonicity-bool .Iso.fun = eval
  canonicity-bool .Iso.inv = fromBool
  canonicity-bool .Iso.sec = λ { true → eval-t ; false → eval-f }
  canonicity-bool .Iso.ret e =
    Sum.elim {C = λ _ → fromBool (eval e) ≡ e}
      (λ p → cong (λ x → fromBool (eval x)) p ∙ cong fromBool eval-t ∙ sym p)
      (λ q → cong (λ x → fromBool (eval x)) q ∙ cong fromBool eval-f ∙ sym q)
      (canonicalize-bool e)

module NatIso
  {ℓ} {[nat] : Type ℓ}
  (numeral : ℕ → [nat])
  (eval : [nat] → ℕ)
  (eval-numeral : ∀ n → eval (numeral n) ≡ n)
  (canonicalize-nat : ∀ e → fiber numeral e)
  where

  canonicity-nat : Iso [nat] ℕ
  canonicity-nat .Iso.fun = eval
  canonicity-nat .Iso.inv = numeral
  canonicity-nat .Iso.sec = eval-numeral
  canonicity-nat .Iso.ret [n] =
    cong numeral (cong eval (sym p) ∙ eval-numeral m) ∙ p
    where
    m = canonicalize-nat [n] .fst
    p = canonicalize-nat [n] .snd
