{-# OPTIONS --cubical --type-in-type #-}

module HyperDoc.Operational.Effects.TermOrdering where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
import Cubical.Foundations.Isomorphism as Iso
import Cubical.Data.Empty as ⊥
open import Cubical.Data.FinData
import Cubical.Data.FinData as Fin
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Bijections.Product
open import Cubical.Data.Nat.Bijections.Sum
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
import Cubical.Data.DescendingList.Strict.Properties as Strict

open import HyperDoc.Algebra.Base

data MonOp : Type where
  e ⊗ : MonOp

MonΣ : Signature
MonΣ .Op = MonOp
MonΣ .arity e = 0
MonΣ .arity ⊗ = 2

module OrderedTerm
  (X : Type)
  (encodeX : X → ℕ)
  (decodeX : ℕ → X)
  (decode-encodeX : (x : X) → decodeX (encodeX x) ≡ x)
  where

  TermX : Type
  TermX = FreeOn MonΣ X

  private
    Tag : Type
    Tag = ℕ ⊎ (ℕ ⊎ ℕ)

    tag : Tag → ℕ
    tag (inl n) = Iso.Iso.fun ℕ⊎ℕ≅ℕ (inl n)
    tag (inr s) =
      Iso.Iso.fun ℕ⊎ℕ≅ℕ
        (inr (Iso.Iso.fun ℕ⊎ℕ≅ℕ s))

    untag-sum : ℕ ⊎ ℕ → Tag
    untag-sum (inl k) = inl k
    untag-sum (inr k) =
      inr (Iso.Iso.inv ℕ⊎ℕ≅ℕ k)

    untag : ℕ → Tag
    untag n =
      untag-sum (Iso.Iso.inv ℕ⊎ℕ≅ℕ n)

    untag-tag : (s : Tag) → untag (tag s) ≡ s
    untag-tag (inl n) =
      cong untag-sum
        (Iso.Iso.ret ℕ⊎ℕ≅ℕ (inl n))
    untag-tag (inr s) =
      cong untag-sum
        (Iso.Iso.ret ℕ⊎ℕ≅ℕ
          (inr (Iso.Iso.fun ℕ⊎ℕ≅ℕ s)))
      ∙ cong inr (Iso.Iso.ret ℕ⊎ℕ≅ℕ s)

    pair : ℕ → ℕ → ℕ
    pair m n =
      Iso.Iso.fun ℕ×ℕ≅ℕ (m , n)

    unpair : ℕ → ℕ × ℕ
    unpair = Iso.Iso.inv ℕ×ℕ≅ℕ

  encode : TermX → ℕ
  encode (inc x) = tag (inl (encodeX x))
  encode (ops e args) = tag (inr (inl 0))
  encode (ops ⊗ args) =
    tag (inr (inr
      (pair (encode (args zero))
            (encode (args (suc zero))))))
  encode (trunc x y p q i j) =
    isSetℕ
      (encode x) (encode y)
      (cong encode p) (cong encode q) i j

  {-# TERMINATING #-}
  mutual
    decode : ℕ → TermX
    decode n = decode-tag (untag n)

    decode-tag : Tag → TermX
    decode-tag (inl k) = inc (decodeX k)
    decode-tag (inr (inl _)) = ops e λ ()
    decode-tag (inr (inr k)) =
      ops ⊗
        (Fin.rec
          (decode (fst (unpair k)))
          (decode (snd (unpair k))))

  fin2-path :
    ∀ {A : Type} (f g : Fin 2 → A) →
    f zero ≡ g zero →
    f (suc zero) ≡ g (suc zero) →
    f ≡ g
  fin2-path f g p₀ p₁ =
    funExt λ i →
      sym (cong f (Iso.Iso.ret finSucMaybeIso i))
      ∙ cases (Iso.Iso.fun finSucMaybeIso i)
      ∙ cong g (Iso.Iso.ret finSucMaybeIso i)
    where
    cases :
      (m : Maybe (Fin 1)) →
      f (Iso.Iso.inv finSucMaybeIso m) ≡
      g (Iso.Iso.inv finSucMaybeIso m)
    cases nothing = p₀
    cases (just j) =
      sym
        (cong (λ k → f (suc k))
          (isContrFin1 .snd j))
      ∙ p₁
      ∙ cong (λ k → g (suc k))
          (isContrFin1 .snd j)

  decode-encode : (t : TermX) → decode (encode t) ≡ t
  decode-encode (inc x) =
    cong decode-tag (untag-tag (inl (encodeX x)))
    ∙ cong inc (decode-encodeX x)
  decode-encode (ops e args) =
    cong decode-tag (untag-tag (inr (inl 0)))
    ∙ cong (ops e)
        (funExt λ i → ⊥.rec (¬Fin0 i))
  decode-encode (ops ⊗ args) =
    cong decode-tag
      (untag-tag
        (inr (inr
          (pair (encode (args zero))
                (encode (args (suc zero)))))))
    ∙ cong (ops ⊗)
        (cong
          (λ p →
            Fin.rec
              (decode (fst p))
              (decode (snd p)))
          (Iso.Iso.ret ℕ×ℕ≅ℕ
            (encode (args zero) ,
             encode (args (suc zero)))))
    ∙ cong (ops ⊗)
        (fin2-path
          (Fin.rec
            (decode (encode (args zero)))
            (decode (encode (args (suc zero)))))
          args
          (decode-encode (args zero))
          (decode-encode (args (suc zero))))
  decode-encode (trunc x y p q i j) =
    isProp→PathP
      (λ j → trunc _ _)
      (decode-encode (p i))
      (decode-encode (q i))
      j

  encode-injective :
    ∀ {x y : TermX} →
    encode x ≡ encode y → x ≡ y
  encode-injective {x} {y} p =
    sym (decode-encode x)
    ∙ cong decode p
    ∙ decode-encode y

  discreteTerm : Discrete TermX
  discreteTerm x y
    with discreteℕ (encode x) (encode y)
  ... | yes p = yes (encode-injective p)
  ... | no ¬p =
    no (λ p → ¬p (cong encode p))

  _>Term_ : TermX → TermX → Type
  x >Term y = encode y < encode x

  >Term-isProp : ∀ {x y} → isProp (x >Term y)
  >Term-isProp {x} {y} = isProp≤

  term-tri :
    ∀ x y →
    Strict.Tri TermX _>Term_
      (y >Term x) (x ≡ y) (x >Term y)
  term-tri x y with encode x ≟ encode y
  ... | Trichotomy.lt p =
    Strict.tri-<
      p
      (λ q →
        ¬m<m
          (subst (encode x <_)
            (sym (cong encode q)) p))
      (λ q → ¬m<m (<-trans p q))
  ... | Trichotomy.eq p =
    Strict.tri-≡
      (λ q →
        ¬m<m (subst (_< encode y) p q))
      (encode-injective p)
      (λ q →
        ¬m<m (subst (encode y <_) p q))
  ... | Trichotomy.gt p =
    Strict.tri->
      (λ q → ¬m<m (<-trans q p))
      (λ q →
        ¬m<m
          (subst (encode y <_)
            (cong encode q) p))
      p

  >Term-trans :
    ∀ {x y z} →
    x >Term y → y >Term z → x >Term z
  >Term-trans {x} {y} {z} x>y y>z =
    <-trans y>z x>y

  >Term-irrefl : ∀ {x} → ¬ x >Term x
  >Term-irrefl {x} = ¬m<m
