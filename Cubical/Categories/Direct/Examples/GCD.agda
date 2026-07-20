{-# OPTIONS --lossy-unification #-}
-- Intrinsically verified Euclidean algorithm as a hylomorphism
-- Adapted from Alexandru, Urbat, Wißmann
-- https://git8.cs.fau.de/software/intrinsically-recursive
module Cubical.Categories.Direct.Examples.GCD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Nat.Mod using (_mod_ ; mod<)
open import Cubical.Data.Nat.GCD
  using (isGCD ; GCD ; isPropGCD ; zeroGCD ; stepGCD)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder ; <→Wo<)
open import Cubical.Categories.Direct.Instances.Poset using (PosetDirect)
import Cubical.Categories.Direct.LocallyContractive as LC

open Functor

private
  dir = PosetDirect (pullbackWFOrder ℕWFOrder (isSet× isSetℕ isSetℕ) snd)

open DirectNotation dir using (_≺_)

Fam : Category _ _
Fam = LC.Fam dir

Hob : Category.ob Fam → Category.ob Fam
Hob A (m , n) =
    ( ( n ≡ 0 )
    ⊎ ( Σ[ n₀ ∈ ℕ ] (n ≡ suc n₀) × ⟨ A (suc n₀ , m mod suc n₀) ⟩ ) )
  , isSet⊎ (isProp→isSet (isSetℕ n 0))
           (isSetΣ isSetℕ λ n₀ →
             isSet× (isProp→isSet (isSetℕ n (suc n₀)))
                    (A (suc n₀ , m mod suc n₀) .snd))

mod≺ : ∀ {m n} n₀ → n ≡ suc n₀ → (suc n₀ , m mod suc n₀) ≺ (m , n)
mod≺ {m} n₀ e =
  subst (λ z → (suc n₀ , m mod suc n₀) ≺ (m , z)) (sym e) (<→Wo< (mod< n₀ m))

Hmap : {A B : Category.ob Fam} (x : ℕ × ℕ)
     → (∀ {y} → y ≺ x → ⟨ A y ⟩ → ⟨ B y ⟩)
     → ⟨ Hob A x ⟩ → ⟨ Hob B x ⟩
Hmap (m , n) f (inl e)            = inl e
Hmap (m , n) f (inr (n₀ , e , a)) = inr (n₀ , e , f (mod≺ n₀ e) a)

Hhom : {A B : Category.ob Fam} → Fam [ A , B ] → Fam [ Hob A , Hob B ]
Hhom {A} {B} h x = Hmap {A} {B} x (λ {y} _ → h y)

H : Functor Fam Fam
H .F-ob A          = Hob A
H .F-hom {A} {B} h = Hhom {A} {B} h
H .F-id            = funExt λ _ → funExt λ { (inl _) → refl ; (inr _) → refl }
H .F-seq _ _       = funExt λ _ → funExt λ { (inl _) → refl ; (inr _) → refl }

Hδ : LC.▷HomActionFam dir H
Hδ {A} {B} x β = Hmap {A} {B} x (λ q → LC.▷app dir β (inl q) q)

Hlc : LC.LocallyContractiveFam dir
Hlc = H , Hδ , λ h x → funExt λ { (inl _) → refl ; (inr _) → refl }

Inp Out : Category.ob Fam
Inp _       = Unit , isSetUnit
Out (m , n) = GCD m n , isProp→isSet isPropGCD

coalg : Fam [ Inp , H .F-ob Inp ]
coalg (m , zero)   tt = inl refl
coalg (m , suc n₀) tt = inr (n₀ , refl , tt)

alg : Fam [ H .F-ob Out , Out ]
alg (m , n) (inl e) =
  m , subst (λ z → isGCD m z m) (sym e) (zeroGCD m)
alg (m , n) (inr (n₀ , e , (d , dGCD))) =
  d , subst (λ z → isGCD m z d) (sym e) (stepGCD dGCD)

private
  module HF = LC.HyloFam dir Hlc Inp Out coalg alg

gcdGCD : ∀ m n → GCD m n
gcdGCD m n = HF.hylo .fst (m , n) tt

gcd : ℕ → ℕ → ℕ
gcd m n = gcdGCD m n .fst

gcdIsGCD : ∀ m n → isGCD m n (gcd m n)
gcdIsGCD m n = gcdGCD m n .snd

gcd-0 : ∀ m → gcd m 0 ≡ m
gcd-0 m = cong fst (HF.hylo-unfold (m , 0) tt)

gcd-suc : ∀ m n₀ → gcd m (suc n₀) ≡ gcd (suc n₀) (m mod suc n₀)
gcd-suc m n₀ = cong fst (HF.hylo-unfold (m , suc n₀) tt)

_ : gcd 12 8 ≡ 4
_ = refl

_ : gcd 48 36 ≡ 12
_ = refl

_ : gcd 96 15 ≡ 3
_ = refl
