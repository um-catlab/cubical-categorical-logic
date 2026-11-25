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
open import Cubical.Categories.Limits.Cartesian.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.ChosenReind
open import
  Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
  using (module ExponentialᴰNotation)
open import Cubical.Categories.Displayed.Instances.Codomain.Sets

open import Cubical.Categories.Instances.Free.Lambda.Negative

open import Gluing.Canonicity

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

  seq,x= : ∀ {Θ Δ Γ A} (γ : Tm Θ Δ) (δ : Tm Δ Γ) (M : Tm Δ (x: A))
    → seqS γ (δ ,x= M) ≡ (seqS γ δ ,x= seqS γ M)
  seq,x= γ δ M = ,x=η _
    ∙ cong₂ _,x=_ (seqAssoc _ _ _ ∙ cong (seqS γ) wkβ)
      (seqAssoc _ _ _ ∙ cong (seqS γ) varβ)

  Pts : Functor LAMBDA (SET ℓ-zero)
  Pts = LAMBDA [ [] ,-]

  private
    F-× : ∀ A → preservesProvidedBinProductsWith Pts (EXTENSION A)
    F-× A Γ = CorepCartesian-at LAMBDA (EXTENSION A Γ)

  CF : ∀ A → Tm [] (x: (↑ A)) → hSet ℓ-zero
  CF A M = fiber quoteCan M
    , isSetΣ (isSetCanonicalForm A) (λ _ → isProp→isSet (isSetTm _ _))

  GLUE = F*Cᴰ SETCC Pts F-× SETCodCCCⱽ

  ⟦_⟧ : ∀ Γ → Categoryᴰ.ob[ GLUE ] Γ
  ⟦_⟧ = elimCtx GLUE (F*Termᴰ SETCC Pts F-× SETCodCCCⱽ)
    (F*BPᴰ SETCC Pts F-× SETCodCCCⱽ) (F*Expᴰ SETCC Pts F-× SETCodCCCⱽ)
    (F*1ᴰ SETCC Pts F-× SETCodCCCⱽ) (F*×ᴰ SETCC Pts F-× SETCodCCCⱽ) CF

  module ⇒ᴰ {A B} (Aᴰ : Categoryᴰ.ob[ GLUE ] (x: A))
    (Bᴰ : Categoryᴰ.ob[ GLUE ] (x: B)) =
    ExponentialᴰNotation (EXPONENTIALS A B)
      (F*Expᴰ SETCC Pts F-× SETCodCCCⱽ Aᴰ Bᴰ)

  sucBody : GLUE [ seqS (seqS wk [su] ,x= var) [app] ][
    ⟦ [] ,x: (↑ nat) ⟧ , ⟦ x: (↑ nat) ⟧ ]
  sucBody = mk ℓ-zero λ z →
    let n = z .snd .snd .fst .snd .fst .snd .fst
        q = z .snd .snd .fst .snd .fst .snd .snd
          ∙ z .snd .snd .fst .snd .snd
          ∙ cong (λ p → seqS p var) (z .snd .snd .snd)
    in (_ , suc n ,
      cong₂ (λ a b → seqS (a ,x= b) [app])
        (canLem {γ⊤ = seqS (z .fst) wk} ∙ seqAssoc _ _ _) q
      ∙ cong (λ a → seqS a [app]) (sym (seq,x= (z .fst) _ var))
      ∙ seqAssoc _ _ _) , refl

  ıc : ∀ {A} (f : FunSym A) → GLUE [ gen f ][ ⟦ [] ⟧ , ⟦ x: A ⟧ ]
  ıc (tr Eq.refl) = mk ℓ-zero λ z → (_ , true , canLem) , refl
  ıc (fl Eq.refl) = mk ℓ-zero λ z → (_ , false , canLem) , refl
  ıc (ze Eq.refl) = mk ℓ-zero λ z → (_ , zero , canLem) , refl
  ıc (su Eq.refl) =
    ChosenReind.reind⟨_⟩ (F*cr SETCC Pts F-× SETCodCCCⱽ) (sym (⇒η [su]))
      (⇒ᴰ.λᴰ ⟦ x: (↑ nat) ⟧ ⟦ x: (↑ nat) ⟧ sucBody)

  CAN : Section Pts (SETCod ℓ-zero)
  CAN = elimLocal SETCC Pts F-× SETCodCCCⱽ CF ıc

  can : ∀ {A} (M : Tm [] (x: (↑ A)))
    → Fib ℓ-zero {Y = Pts ⟅ x: (↑ A) ⟆} (CF A) M
  can = canonicalize [] CAN tt*

  eval : ∀ {A} → Tm [] (x: (↑ A)) → CanonicalForm A
  eval M = can M .fst .snd .fst

  can-bool : Iso Bool [bool]
  can-bool .Iso.fun = quoteCan
  can-bool .Iso.inv = eval
  can-bool .Iso.sec M = can M .fst .snd .snd ∙ can M .snd
  can-bool .Iso.ret = Bool.elim refl refl

  can-nat-suc : ∀ n → eval ＂ suc n ＂ℕ ≡ suc (eval ＂ n ＂ℕ)
  can-nat-suc n = refl

  can-nat-ret : ∀ n → eval ＂ n ＂ℕ ≡ n
  can-nat-ret zero = refl
  can-nat-ret (suc n) = can-nat-suc n ∙ cong suc (can-nat-ret n)

  can-nat : Iso ℕ [nat]
  can-nat .Iso.fun = quoteCan
  can-nat .Iso.inv = eval
  can-nat .Iso.sec M = can M .fst .snd .snd ∙ can M .snd
  can-nat .Iso.ret = can-nat-ret

  private
    module Examples where
      sucF : Tm [] (x: (↑ nat [⇒] ↑ nat))
      sucF = [λ] ([APP] (seqS wk [su]) var)

      _ : eval ([APP] sucF ＂ 2 ＂ℕ) ≡ 3
      _ = refl
