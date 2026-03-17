{-
  Canonicity for Negative Lambda calculus with tru, false, zero and successor
-}

{-# OPTIONS --lossy-unification #-}
module Gluing.Lambda.BoolNatCanonicity.Negative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure hiding (⟨_⟩)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq
open import Cubical.Data.Bool as Bool
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Limits.Cartesian.More
open import Cubical.Categories.Displayed.Instances.Reindex.Base

open import Cubical.Categories.Instances.Free.Lambda.Negative

open Category
open Functor
open Section

module _ where
  data OB : Type where
    bool nat : OB

  module _ where
    open Lambda1×⇒Ty.Ty OB
    data FunSym (A : Lambda1×⇒Ty.Ty OB) : Type ℓ-zero where
      tr fl : A Eq.≡ ↑ bool → FunSym A
      ze : A Eq.≡ ↑ nat → FunSym A
      su : A Eq.≡ (↑ nat [⇒] ↑ nat) → FunSym A

  module Lam[b,n] = Lambda1×⇒ OB FunSym
  open Lam[b,n]

  [bool] = Tm [] (x: (↑ bool))
  [nat] = Tm [] (x: (↑ nat))
  [tr] [fl] : [bool]
  [tr] = gen (tr Eq.refl)
  [fl] = gen (fl Eq.refl)

  ＂_＂Bool : Bool → [bool]
  ＂_＂Bool = if_then [tr] else [fl]

  [ze] : [nat]
  [su] : Tm [] (x: (↑ nat [⇒] ↑ nat))
  [ze] = gen (ze Eq.refl)
  [su] = gen (su Eq.refl)

  ＂_＂ℕ : ℕ → [nat]
  ＂ n ＂ℕ = iter n (λ M → [APP] [su] M) [ze]

  CanonicalForm : OB → Type ℓ-zero
  CanonicalForm bool = Bool
  CanonicalForm nat = ℕ

  isSetCanonicalForm : ∀ A → isSet (CanonicalForm A)
  isSetCanonicalForm bool = isSetBool
  isSetCanonicalForm nat = isSetℕ

  quoteCan : ∀ {A} → CanonicalForm A → Tm [] (x: (↑ A))
  quoteCan {A = bool} = ＂_＂Bool
  quoteCan {A = nat} = ＂_＂ℕ

  canLem : ∀ {A} {γ⊤ : Tm [] []} {f : Tm [] A} → f ≡ seqS γ⊤ f
  canLem = sym (LAMBDA.⋆IdL _) ∙ LAMBDA.⟨ sym ([]η _ ∙ sym ([]η LAMBDA.id) ) ⟩⋆⟨ refl ⟩

  CAN : Section (LAMBDA [ Ctx.[] ,-]) (SETᴰ ℓ-zero ℓ-zero)
  CAN = elimLocal SETCC ((LAMBDA [ Ctx.[] ,-]))
    (λ A Γ → CorepCartesian-at LAMBDA (EXTENSION A Γ))
    EqSETᴰCCCⱽ
    (λ A M → fiber quoteCan M , isSetΣ (isSetCanonicalForm A) (λ _ → isProp→isSet (isSetTm _ _)))
    λ { (tr Eq.refl) _ _ → true , canLem
      ; (fl Eq.refl) _ _ → false , canLem
      ; (ze Eq.refl) _ _ → zero , canLem
      ; (su Eq.refl) γ⊤ _ M canM → (suc (canM .fst)) ,
        ([APP] [su] (iter (canM .fst) (λ N → seqS ([su] ,x= N) [app]) [ze])
          ≡⟨ cong₂ [APP] canLem (canM .snd ∙ varβ) ⟩
        [APP] (seqS γ⊤ [su]) M  ∎)
      }

  can-bool : Iso Bool (Tm [] (x: (↑ bool)))
  can-bool .Iso.fun = quoteCan
  can-bool .Iso.inv M = CAN .F-homᴰ M  LAMBDA.id _ .fst
  can-bool .Iso.sec M =
    CAN .F-homᴰ M  LAMBDA.id _ .snd ∙ LAMBDA.⋆IdL _
  can-bool .Iso.ret = Bool.elim refl refl
