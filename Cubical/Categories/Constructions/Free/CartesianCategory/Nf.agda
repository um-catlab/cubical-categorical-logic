module Cubical.Categories.Constructions.Free.CartesianCategory.Nf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary

import Cubical.Data.Equality as Eq
open import Cubical.Data.Empty
open import Cubical.Data.Sigma hiding (_×_)
import Cubical.Data.Sigma as Σ
open import Cubical.Data.Unit

open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver

private
  variable
    ℓq ℓq' : Level
  module _ {ℓ} {A : Type ℓ} (A-isSet : isSet A) where
    isEqSet : {a a' : A} → isProp (a Eq.≡ a')
    isEqSet p q = sym (Eq.pathToEq-eqToPath _) ∙ congS Eq.pathToEq (A-isSet _ _ (Eq.eqToPath p) (Eq.eqToPath q)) ∙ Eq.pathToEq-eqToPath _
  module _ {ℓ} {A : Type ℓ} (A-Discrete : Discrete A) where
    DiscreteEq : ∀(a a' : A) → Dec (a Eq.≡ a')
    DiscreteEq a a' with A-Discrete a a'
    ...              | yes p = yes (Eq.pathToEq p)
    ...              | no p = no (p ∘S Eq.eqToPath)
  module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (A-isSet : isSet A) where
    transportEqRefl' : ∀{a : A} {b : B a} {p : a Eq.≡ a} → b ≡ Eq.transport B p b
    transportEqRefl' {p = p} = congS (λ x → Eq.transport B x _) (isEqSet A-isSet Eq.refl p)

module _ (Q : ×Quiver' ℓq ℓq') where
  private
    module Q = ×Quiver'Notation Q
  -- morally, we want normal and neutral terms to be a sort of profunctor on the
  -- syntactic category, but it seems difficult to do that directly, so we'll
  -- first manually define "Type-valued" "profunctors" and prove everything is a
  -- set after the fact
  module _ (Γ : Q.Ob) where
    data NormalForm : (τ : Q.Ob) → Type (ℓ-max ℓq ℓq')
    data NeutralTerm : (τ : Q.Ob) → Type (ℓ-max ℓq ℓq')

    data NeutralTerm where
      var : ∀{τ} → (τ Eq.≡ Γ) → NeutralTerm τ
      proj₁ : ∀{τ₁ τ₂} → NeutralTerm (τ₁ × τ₂) → NeutralTerm τ₁
      proj₂ : ∀{τ₁ τ₂} → NeutralTerm (τ₁ × τ₂) → NeutralTerm τ₂
      symb : ∀{τ} → (f : Q.mor) → τ Eq.≡ ↑ (Q.cod f) → NormalForm (Q.dom f) → NeutralTerm τ

    data NormalForm where
      shift : ∀{x} → NeutralTerm (↑ x) → NormalForm (↑ x)
      pair : ∀{τ₁ τ₂} → NormalForm τ₁ → NormalForm τ₂ → NormalForm (τ₁ × τ₂)
      uniq : NormalForm ⊤

    -- This should be macro-able
    private
      codeNeutralTerm : ∀{τ} → Rel (NeutralTerm τ) (NeutralTerm τ) (ℓ-max ℓq ℓq')
      codeNormalForm : ∀{τ} → Rel (NormalForm τ) (NormalForm τ) (ℓ-max ℓq ℓq')

      codeNeutralTerm (var p) (var q) = Lift {j = ℓq'} (p ≡ q)
      codeNeutralTerm (proj₁ {τ₂ = τ₂} x) (proj₁ {τ₂ = τ₃} y) =
        Σ[ p ∈ τ₂ Eq.≡ τ₃ ] codeNeutralTerm (Eq.transport _ p x) y
      codeNeutralTerm (proj₂ {τ₁ = τ₁} x) (proj₂ {τ₁ = τ₂} y) =
        Σ[ p ∈ τ₁ Eq.≡ τ₂ ] codeNeutralTerm (Eq.transport _ p x) y
      codeNeutralTerm (symb f p x) (symb g q y) =
        Σ[ r ∈ f Eq.≡ g ]
          (Eq.transport _ r p ≡ q) Σ.×
          codeNormalForm (Eq.transport _ r x) y
      codeNeutralTerm x y = ⊥*
      codeNormalForm (shift x) (shift y) = codeNeutralTerm x y
      codeNormalForm (pair x₁ x₂) (pair y₁ y₂) = codeNormalForm x₁ y₁ Σ.× codeNormalForm x₂ y₂
      codeNormalForm uniq uniq = Unit*

      reflCodeNeutralTerm : ∀{τ} → BinaryRelation.isRefl (codeNeutralTerm {τ})
      reflCodeNormalForm : ∀{τ} → BinaryRelation.isRefl (codeNormalForm {τ})

      reflCodeNeutralTerm (var _) = lift refl
      reflCodeNeutralTerm (proj₁ x) = Eq.refl , reflCodeNeutralTerm x
      reflCodeNeutralTerm (proj₂ x) = Eq.refl , reflCodeNeutralTerm x
      reflCodeNeutralTerm (symb f p x) = Eq.refl , refl , reflCodeNormalForm x
      reflCodeNormalForm (shift x) = reflCodeNeutralTerm x
      reflCodeNormalForm (pair x y) = reflCodeNormalForm x , reflCodeNormalForm y
      reflCodeNormalForm uniq = tt*

      encodeNeutralTerm : ∀{τ} → (x y : NeutralTerm τ) → x ≡ y → codeNeutralTerm x y
      encodeNeutralTerm x _ p = subst (codeNeutralTerm x) p (reflCodeNeutralTerm x)

      encodeNormalForm : ∀{τ} → (x y : NormalForm τ) → x ≡ y → codeNormalForm x y
      encodeNormalForm x _ p = subst (codeNormalForm x) p (reflCodeNormalForm x)

      decodeNeutralTerm : ∀{τ} → (x y : NeutralTerm τ) → codeNeutralTerm x y → x ≡ y
      decodeNormalForm : ∀{τ} → (x y : NormalForm τ) → codeNormalForm x y → x ≡ y

      decodeNeutralTerm (var _) (var _) (lift r) = congS var r
      decodeNeutralTerm (proj₁ _) (proj₁ _) (Eq.refl , q) = congS proj₁ (decodeNeutralTerm _ _ q)
      decodeNeutralTerm (proj₂ _) (proj₂ _) (Eq.refl , q) = congS proj₂ (decodeNeutralTerm _ _ q)
      decodeNeutralTerm (symb _ _ _) (symb _ _ _) (Eq.refl , r , s) = cong₂ (symb _) r (decodeNormalForm _ _ s)

      decodeNormalForm (shift _) (shift _) p = congS shift (decodeNeutralTerm _ _ p)
      decodeNormalForm (pair _ _) (pair _ _) (p , q) = cong₂ pair (decodeNormalForm _ _ p) (decodeNormalForm _ _ q)
      decodeNormalForm uniq uniq _ = refl

      inj-var : ∀{τ} {p q : τ Eq.≡ Γ} → var p ≡ var q → p ≡ q
      inj-var r = encodeNeutralTerm _ _ r .lower

      inj-proj₁ : ∀{τ₁ τ₂ τ₃} {x : NeutralTerm (τ₁ × τ₂)} {y : NeutralTerm (τ₁ × τ₃)} →
        proj₁ x ≡ proj₁ y →
        Σ[ p ∈ τ₂ Eq.≡ τ₃ ] Eq.transport _ p x ≡ y
      inj-proj₁ r = map-snd (decodeNeutralTerm _ _) (encodeNeutralTerm _ _ r)

      inj-proj₂ : ∀{τ₁ τ₂ τ₃} {x : NeutralTerm (τ₁ × τ₃)} {y : NeutralTerm (τ₂ × τ₃)} →
        proj₂ x ≡ proj₂ y →
        Σ[ p ∈ τ₁ Eq.≡ τ₂ ] Eq.transport _ p x ≡ y
      inj-proj₂ r = map-snd (decodeNeutralTerm _ _) (encodeNeutralTerm _ _ r)

      inj-symb : ∀{τ} {f g} {p : τ Eq.≡ _} {q : τ Eq.≡ _} {x y} → symb f p x ≡ symb g q y →
        Σ[ r ∈ f Eq.≡ g ] (Eq.transport _ r p ≡ q) Σ.× (Eq.transport _ r x ≡ y)
      inj-symb s = map-snd (map-snd (decodeNormalForm _ _)) (encodeNeutralTerm _ _ s)

      inj-shift : ∀{x} {y z : NeutralTerm (↑ x)} → shift y ≡ shift z → y ≡ z
      inj-shift = decodeNeutralTerm _ _ ∘S encodeNormalForm _ _

      inj-pair : ∀{τ₁ τ₂} {w y : NormalForm τ₁} {x z : NormalForm τ₂} → pair w x ≡ pair y z → (w ≡ y) Σ.× (x ≡ z)
      inj-pair p = map-× (decodeNormalForm _ _) (decodeNormalForm _ _) (encodeNormalForm _ _ p)

    module _ (Discrete-Ob : Discrete Q.Ob) (Discrete-Mor : Discrete Q.mor) where

      DiscreteNeutralTerm : ∀{τ} → Discrete (NeutralTerm τ)
      DiscreteNormalForm : ∀{τ} → Discrete (NormalForm τ)

      DiscreteNeutralTerm (var p) (var q) = yes (congS var (isEqSet (Discrete→isSet Discrete-Ob) p q))
      DiscreteNeutralTerm (var _) (proj₁ _) = no (λ p → subst (λ {(var _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (var _) (proj₂ _) = no (λ p → subst (λ {(var _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (var _) (symb _ _ _) = no (λ p → subst (λ {(var _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (proj₁ _) (var _) = no (λ p → subst (λ {(proj₁ _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (proj₁ {τ₂ = τ₂} x) (proj₁ {τ₂ = τ₃} y) with DiscreteEq Discrete-Ob τ₂ τ₃
      ...                                                         | yes Eq.refl with DiscreteNeutralTerm x y
      ...                                                                       | yes p = yes (congS proj₁ p)
      ...                                                                       | no p = no (λ q → p (transportEqRefl' (Discrete→isSet Discrete-Ob) ∙ inj-proj₁ q .snd))
      DiscreteNeutralTerm (proj₁ {τ₂ = τ₂} x) (proj₁ {τ₂ = τ₃} y) | no p = no (p ∘S fst ∘S inj-proj₁)
      DiscreteNeutralTerm (proj₁ _) (proj₂ _) = no (λ p → subst (λ {(proj₁ _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (proj₁ _) (symb _ _ _) = no (λ p → subst (λ {(proj₁ _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (proj₂ _) (var _) = no (λ p → subst (λ {(proj₂ _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (proj₂ _) (proj₁ _) = no (λ p → subst (λ {(proj₂ _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (proj₂ {τ₁ = τ₁} x) (proj₂ {τ₁ = τ₂} y) with DiscreteEq Discrete-Ob τ₁ τ₂
      ...                                                         | yes Eq.refl with DiscreteNeutralTerm x y
      ...                                                                       | yes p = yes (congS proj₂ p)
      ...                                                                       | no p = no (λ q → p (transportEqRefl' (Discrete→isSet Discrete-Ob) ∙ inj-proj₂ q .snd))
      DiscreteNeutralTerm (proj₂ {τ₁ = τ₁} x) (proj₂ {τ₁ = τ₂} y) | no p = no (p ∘S fst ∘S inj-proj₂)
      DiscreteNeutralTerm (proj₂ _) (symb _ _ _) = no (λ p → subst (λ {(proj₂ _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (symb _ _ _) (var _) = no (λ p → subst (λ {(symb _ _ _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (symb _ _ _) (proj₁ _) = no (λ p → subst (λ {(symb _ _ _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (symb _ _ _) (proj₂ _) = no (λ p → subst (λ {(symb _ _ _) → Unit ; _ → ⊥}) p tt)
      DiscreteNeutralTerm (symb f x₁ x₂) (symb g y₁ y₂) with DiscreteEq Discrete-Mor f g
      ...                                               | yes Eq.refl with DiscreteNormalForm x₂ y₂
      ...                                                             | yes p = yes (cong₂ (symb f) (isEqSet (Discrete→isSet Discrete-Ob) _ _) p)
      ...                                                             | no p = no (λ q → p (transportEqRefl' (Discrete→isSet Discrete-Mor) ∙ inj-symb q .snd .snd))
      DiscreteNeutralTerm (symb f x₁ x₂) (symb g y₁ y₂) | no p = no (p ∘S fst ∘S inj-symb)

      DiscreteNormalForm (shift x) (shift y) with DiscreteNeutralTerm x y
      ...                                    | yes p = yes (congS shift p)
      ...                                    | no p = no (p ∘S inj-shift)
      DiscreteNormalForm (pair w x) (pair y z) with DiscreteNormalForm w y , DiscreteNormalForm x z
      ...                                      | yes p , yes q = yes (cong₂ pair p q)
      ...                                      | no p , _ = no (p ∘S fst ∘S inj-pair)
      ...                                      | _ , no p = no (p ∘S snd ∘S inj-pair)
      DiscreteNormalForm uniq uniq = yes refl
