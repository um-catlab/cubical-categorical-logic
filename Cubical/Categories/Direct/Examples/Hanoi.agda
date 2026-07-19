{-# OPTIONS --lossy-unification #-}
-- The tower of Hanoi as a hylomorphism
module Cubical.Categories.Direct.Examples.Hanoi where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ ; +-suc)
open import Cubical.Data.Nat.Order.Recursive using (≤-refl)
open import Cubical.Data.Fin using (Fin ; isSetFin)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.List.Properties using (isOfHLevelList ; length++)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)
open import Cubical.Categories.Direct.Instances.Poset using (PosetDirect)
import Cubical.Categories.Direct.LocallyContractive as LC

open Functor

private
  dir = PosetDirect ℕWFOrder

open DirectNotation dir using (_≺_ ; isProp≺)

Fam : Category _ _
Fam = LC.Fam dir

Peg : Type ℓ-zero
Peg = Fin 3

isSetPeg : isSet Peg
isSetPeg = isSetFin

Move : Type ℓ-zero
Move = Peg × Peg

isSetMove : isSet Move
isSetMove = isSet× isSetPeg isSetPeg

Hob : Category.ob Fam → Category.ob Fam
Hob A n = (Unit ⊎ (Σ[ m ∈ ℕ ] (m ≺ n) × Peg × Peg × ⟨ A m ⟩ × ⟨ A m ⟩))
        , isSet⊎ isSetUnit
            (isSetΣ isSetℕ λ m →
              isSet× (isProp→isSet (isProp≺ m n))
                (isSet× isSetPeg
                  (isSet× isSetPeg
                    (isSet× (A m .snd) (A m .snd)))))

Hmap : {A B : Category.ob Fam} (n : ℕ)
     → (∀ {m} → m ≺ n → ⟨ A m ⟩ → ⟨ B m ⟩)
     → ⟨ Hob A n ⟩ → ⟨ Hob B n ⟩
Hmap n f (inl tt) = inl tt
Hmap n f (inr (m , lt , from , to , d₁ , d₂)) =
  inr (m , lt , from , to , f lt d₁ , f lt d₂)

Hhom : {A B : Category.ob Fam} → Fam [ A , B ] → Fam [ Hob A , Hob B ]
Hhom {A} {B} h n = Hmap {A} {B} n (λ {m} _ → h m)

H : Functor Fam Fam
H .F-ob A          = Hob A
H .F-hom {A} {B} h = Hhom {A} {B} h
H .F-id            = funExt λ _ → funExt λ { (inl _) → refl ; (inr _) → refl }
H .F-seq _ _       = funExt λ _ → funExt λ { (inl _) → refl ; (inr _) → refl }

Hδ : LC.▷HomActionFam dir H
Hδ {A} {B} n β = Hmap {A} {B} n (λ q → LC.▷app dir β (inl q) q)

Hlc : LC.LocallyContractiveFam dir
Hlc = H , Hδ , λ h n → funExt λ { (inl _) → refl ; (inr _) → refl }

Inp Out : Category.ob Fam
Inp _ = (Peg × Peg × Peg) , isSet× isSetPeg (isSet× isSetPeg isSetPeg)
Out _ = List Move , isOfHLevelList 0 isSetMove

coalg : Fam [ Inp , H .F-ob Inp ]
coalg zero     _                = inl tt
coalg (suc n₀) (from , to , aux) =
  inr (n₀ , ≤-refl n₀ , from , to , (from , aux , to) , (aux , to , from))

alg : Fam [ H .F-ob Out , Out ]
alg n (inl tt)                            = []
alg n (inr (m , _ , from , to , d₁ , d₂)) = d₁ ++ ((from , to) ∷ d₂)

private
  module HF = LC.HyloFam dir Hlc Inp Out coalg alg

hanoi : ℕ → Peg → Peg → Peg → List Move
hanoi n from to aux = HF.hylo .fst n (from , to , aux)

hanoi-0 : ∀ from to aux → hanoi 0 from to aux ≡ []
hanoi-0 from to aux = HF.hylo-unfold 0 (from , to , aux)

hanoi-suc : ∀ n₀ from to aux
          → hanoi (suc n₀) from to aux
          ≡ hanoi n₀ from aux to ++ ((from , to) ∷ hanoi n₀ aux to from)
hanoi-suc n₀ from to aux = HF.hylo-unfold (suc n₀) (from , to , aux)

-- 2^n - 1
hanoiLen : ℕ → ℕ
hanoiLen zero    = 0
hanoiLen (suc n) = suc (hanoiLen n + hanoiLen n)

length-hanoi : ∀ n from to aux
  → length (hanoi n from to aux) ≡ hanoiLen n
length-hanoi zero    from to aux = cong length (hanoi-0 from to aux)
length-hanoi (suc n) from to aux =
  cong length (hanoi-suc n from to aux)
  ∙ length++ (hanoi n from aux to) ((from , to) ∷ hanoi n aux to from)
  ∙ cong₂ (λ a b → a + suc b)
      (length-hanoi n from aux to) (length-hanoi n aux to from)
  ∙ +-suc (hanoiLen n) (hanoiLen n)

p0 p1 p2 : Peg
p0 = 0 , tt
p1 = 1 , tt
p2 = 2 , tt

_ : hanoi 2 p0 p2 p1
  ≡ ((p0 , p1) ∷ (p0 , p2) ∷ (p1 , p2) ∷ [])
_ = refl
