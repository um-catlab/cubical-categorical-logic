{-# OPTIONS --lossy-unification #-}
-- Intrinsically verified Karatsuba multiplication as a hylomorphism
module Cubical.Categories.Direct.Examples.Karatsuba where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.Nat
  using (ℕ ; zero ; suc ; isSetℕ ; _+_ ; _·_ ; _∸_)
open import Cubical.Data.Nat.Properties using (+-assoc ; ∸+)
open import Cubical.Data.Nat.Mod
  using (≡remainder+quotient ; remainder_/_ ; quotient_/_)
open import Cubical.Tactics.NatSolver using (solveℕ!)

import Cubical.Data.Nat.Order as Ord

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder ; <→Wo<)
open import Cubical.Categories.Direct.Instances.Poset using (PosetDirect)
import Cubical.Categories.Direct.LocallyContractive as LC

open Functor

private
  dir = PosetDirect
    (pullbackWFOrder ℕWFOrder (isSet× (isSet× isSetℕ isSetℕ) isSetℕ) snd)

open DirectNotation dir using (_≺_ ; isProp≺)

Fam : Category _ _
Fam = LC.Fam dir

B : ℕ
B = 2

_^B : ℕ → ℕ
zero  ^B = 1
suc h ^B = B · (h ^B)

⌊_/2⌋ : ℕ → ℕ
⌊ zero /2⌋        = zero
⌊ suc zero /2⌋    = zero
⌊ suc (suc n) /2⌋ = suc ⌊ n /2⌋

half≤ : ∀ n → ⌊ n /2⌋ Ord.≤ n
half≤ zero          = Ord.≤-refl
half≤ (suc zero)    = Ord.≤-suc Ord.≤-refl
half≤ (suc (suc n)) = Ord.suc-≤-suc (Ord.≤-suc (half≤ n))

half< : ∀ n → ⌊ suc (suc n) /2⌋ Ord.< suc (suc n)
half< n = Ord.suc-≤-suc (Ord.suc-≤-suc (half≤ n))

private
  ∸∸-cancel : ∀ a b c → (a + b + c) ∸ a ∸ b ≡ c
  ∸∸-cancel a b c =
    cong (_∸ b) (cong (_∸ a) (sym (+-assoc a b c)) ∙ ∸+ (b + c) a) ∙ ∸+ c b

  karatsuba-identity : ∀ xlo xhi ylo yhi Bh →
      xhi · yhi · (Bh · Bh)
        + (((xhi + xlo) · (yhi + ylo) ∸ xhi · yhi ∸ xlo · ylo) · Bh + xlo · ylo)
    ≡ (xlo + Bh · xhi) · (ylo + Bh · yhi)
  karatsuba-identity xlo xhi ylo yhi Bh =
      cong (λ w → xhi · yhi · (Bh · Bh) + (w · Bh + xlo · ylo)) subeq ∙ final
    where
      crosseq : (xhi + xlo) · (yhi + ylo)
              ≡ xhi · yhi + xlo · ylo + (xhi · ylo + xlo · yhi)
      crosseq = solveℕ!

      subeq : (xhi + xlo) · (yhi + ylo) ∸ xhi · yhi ∸ xlo · ylo
            ≡ xhi · ylo + xlo · yhi
      subeq = cong (λ w → w ∸ xhi · yhi ∸ xlo · ylo) crosseq
            ∙ ∸∸-cancel (xhi · yhi) (xlo · ylo) (xhi · ylo + xlo · yhi)

      final : xhi · yhi · (Bh · Bh) + ((xhi · ylo + xlo · yhi) · Bh + xlo · ylo)
            ≡ (xlo + Bh · xhi) · (ylo + Bh · yhi)
      final = solveℕ!

Hob : Category.ob Fam → Category.ob Fam
Hob A ((x , y) , k) =
    ( Unit
    ⊎ ( Σ[ xlo ∈ ℕ ] Σ[ xhi ∈ ℕ ] Σ[ ylo ∈ ℕ ] Σ[ yhi ∈ ℕ ]
        Σ[ Bh ∈ ℕ ] Σ[ k' ∈ ℕ ]
          (((xlo , ylo) , k') ≺ ((x , y) , k))
          × (x ≡ xlo + Bh · xhi) × (y ≡ ylo + Bh · yhi)
          × ⟨ A ((xlo , ylo) , k') ⟩
          × ⟨ A ((xhi + xlo , yhi + ylo) , k') ⟩
          × ⟨ A ((xhi , yhi) , k') ⟩ ) )
  , isSet⊎ isSetUnit
      (isSetΣ isSetℕ λ xlo → isSetΣ isSetℕ λ xhi → isSetΣ isSetℕ λ ylo →
       isSetΣ isSetℕ λ yhi → isSetΣ isSetℕ λ Bh → isSetΣ isSetℕ λ k' →
         isSet× (isProp→isSet (isProp≺ _ _))
         (isSet× (isProp→isSet (isSetℕ _ _))
         (isSet× (isProp→isSet (isSetℕ _ _))
         (isSet× (A ((xlo , ylo) , k') .snd)
         (isSet× (A ((xhi + xlo , yhi + ylo) , k') .snd)
                 (A ((xhi , yhi) , k') .snd))))))

Hmap : {A B : Category.ob Fam} (idx : (ℕ × ℕ) × ℕ)
     → (∀ {y} → y ≺ idx → ⟨ A y ⟩ → ⟨ B y ⟩)
     → ⟨ Hob A idx ⟩ → ⟨ Hob B idx ⟩
Hmap idx f (inl tt) = inl tt
Hmap idx f
  (inr (xlo , xhi , ylo , yhi , Bh , k' , lt , px , py , a0 , a1 , a2)) =
  inr ( xlo , xhi , ylo , yhi , Bh , k' , lt , px , py
      , f lt a0 , f lt a1 , f lt a2 )

Hhom : {A B : Category.ob Fam} → Fam [ A , B ] → Fam [ Hob A , Hob B ]
Hhom {A} {B} h idx = Hmap {A} {B} idx (λ {y} _ → h y)

H : Functor Fam Fam
H .F-ob A          = Hob A
H .F-hom {A} {B} h = Hhom {A} {B} h
H .F-id            = funExt λ _ → funExt λ { (inl _) → refl ; (inr _) → refl }
H .F-seq _ _       = funExt λ _ → funExt λ { (inl _) → refl ; (inr _) → refl }

Hδ : LC.▷HomActionFam dir H
Hδ {A} {B} idx β = Hmap {A} {B} idx (λ q → LC.▷app dir β (inl q) q)

Hlc : LC.LocallyContractiveFam dir
Hlc = H , Hδ , λ h idx → funExt λ { (inl _) → refl ; (inr _) → refl }

Inp : Category.ob Fam
Inp _ = Unit , isSetUnit

Out : Category.ob Fam
Out ((x , y) , k) = (Σ[ p ∈ ℕ ] (p ≡ x · y))
                  , isSetΣ isSetℕ λ p → isProp→isSet (isSetℕ p (x · y))

coalg : Fam [ Inp , H .F-ob Inp ]
coalg ((x , y) , zero)         tt = inl tt
coalg ((x , y) , suc zero)     tt = inl tt
coalg ((x , y) , suc (suc k₀)) tt =
  inr ( remainder x / Bh , quotient x / Bh , remainder y / Bh , quotient y / Bh
      , Bh , ⌊ suc (suc k₀) /2⌋
      , <→Wo< (half< k₀)
      , sym (≡remainder+quotient Bh x)
      , sym (≡remainder+quotient Bh y)
      , tt , tt , tt )
  where
    Bh : ℕ
    Bh = ⌊ suc (suc k₀) /2⌋ ^B

alg : Fam [ H .F-ob Out , Out ]
alg ((x , y) , k) (inl tt) = x · y , refl
alg ((x , y) , k)
  (inr (xlo , xhi , ylo , yhi , Bh , k' , _ , px , py
       , (p0 , e0) , (p1 , e1) , (p2 , e2))) =
  p2 · (Bh · Bh) + ((p1 ∸ p2 ∸ p0) · Bh + p0) , proof
  where
    valeq : p2 · (Bh · Bh) + ((p1 ∸ p2 ∸ p0) · Bh + p0)
          ≡ xhi · yhi · (Bh · Bh)
              + (((xhi + xlo) · (yhi + ylo) ∸ xhi · yhi ∸ xlo · ylo) · Bh
                 + xlo · ylo)
    valeq i = (e2 i) · (Bh · Bh) + (((e1 i) ∸ (e2 i) ∸ (e0 i)) · Bh + (e0 i))

    proof : p2 · (Bh · Bh) + ((p1 ∸ p2 ∸ p0) · Bh + p0) ≡ x · y
    proof = valeq
          ∙ karatsuba-identity xlo xhi ylo yhi Bh
          ∙ cong₂ _·_ (sym px) (sym py)

private
  module HF = LC.HyloFam dir Hlc Inp Out coalg alg

limbsFuel : ℕ → ℕ → ℕ
limbsFuel zero      _       = zero
limbsFuel (suc _)   zero    = zero
limbsFuel (suc fu)  (suc n) = suc (limbsFuel fu ⌊ suc n /2⌋)

limbsOf : ℕ → ℕ
limbsOf n = limbsFuel n n

kmulΣ : (x y : ℕ) → Σ[ p ∈ ℕ ] (p ≡ x · y)
kmulΣ x y = HF.hylo .fst ((x , y) , limbsOf (x + y)) tt

kmul : ℕ → ℕ → ℕ
kmul x y = kmulΣ x y .fst

kmul-correct : ∀ x y → kmul x y ≡ x · y
kmul-correct x y = kmulΣ x y .snd

_ : kmul 0 0 ≡ 0
_ = refl

_ : kmul 1 1 ≡ 1
_ = refl

_ : kmul 3 5 ≡ 15
_ = refl

_ : kmul 12 12 ≡ 144
_ = refl
