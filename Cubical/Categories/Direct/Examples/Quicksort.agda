{-# OPTIONS --lossy-unification #-}
-- Intrinsically correct quicksort as a hylomorphism
--
-- Adapted from Alexandru, Urbat, Wißmann
-- https://git8.cs.fau.de/software/intrinsically-recursive
module Cubical.Categories.Direct.Examples.Quicksort where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; false≢true ; true≢false)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive using (_≤_)
import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.List.More
  using (All ; module Ordered ; filterL ; filter-length ; All-filter-sound)
open import Cubical.Data.Empty as ⊥ using (⊥)
import Cubical.HITs.FiniteMultiset as FMS

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Bag
  using (Bag ; BagDirect ; lengthFM ; fromList ; fromList-++
        ; lengthFM-fromList ; bagShuffle ; partitionBag
        ; AllFM ; All→AllFM ; AllFM→All)
import Cubical.Categories.Direct.LocallyContractive as LC

open Functor

private
  dir = BagDirect ℕ

open DirectNotation dir using (_≺_ ; isProp≺)

Fam : Category _ _
Fam = LC.Fam dir

leq : ℕ → ℕ → Bool
leq zero    _       = true
leq (suc m) zero    = false
leq (suc m) (suc n) = leq m n

leq-true : ∀ y x → leq y x ≡ true → y ≤ x
leq-true zero    x       _ = tt
leq-true (suc y) zero    e = ⊥.rec (false≢true e)
leq-true (suc y) (suc x) e = leq-true y x e

leq-false : ∀ y x → leq y x ≡ false → x ≤ y
leq-false zero    x       e = ⊥.rec (true≢false e)
leq-false (suc y) zero    e = tt
leq-false (suc y) (suc x) e = leq-false y x e

not-true : ∀ b → not b ≡ true → b ≡ false
not-true false _ = refl
not-true true  e = ⊥.rec (false≢true e)

lows highs : ℕ → List ℕ → List ℕ
lows  piv xs = filterL (λ y → leq y piv) xs
highs piv xs = filterL (λ y → not (leq y piv)) xs

open Ordered _≤_ Ord.isProp≤ Ord.≤-trans

Q≤ Q≥ : ℕ → ℕ → hProp ℓ-zero
Q≤ piv z = (z ≤ piv) , Ord.isProp≤ {z} {piv}
Q≥ piv z = (piv ≤ z) , Ord.isProp≤ {piv} {z}

Hob : Category.ob Fam → Category.ob Fam
Hob A b =
  ( (b ≡ FMS.[])
  ⊎ ( Σ[ piv ∈ ℕ ] Σ[ lo ∈ Bag ℕ ] Σ[ hi ∈ Bag ℕ ]
        (lo ≺ b) × (hi ≺ b)
        × (b ≡ lo FMS.++ (piv FMS.∷ hi))
        × ⟨ AllFM (Q≤ piv) lo ⟩ × ⟨ AllFM (Q≥ piv) hi ⟩
        × ⟨ A lo ⟩ × ⟨ A hi ⟩ ) )
  , isSet⊎ (isProp→isSet (FMS.trunc _ _))
      (isSetΣ isSetℕ λ piv → isSetΣ FMS.trunc λ lo → isSetΣ FMS.trunc λ hi →
        isSet× (isProp→isSet (isProp≺ lo b))
        (isSet× (isProp→isSet (isProp≺ hi b))
        (isSet× (isProp→isSet (FMS.trunc _ _))
        (isSet× (isProp→isSet (AllFM (Q≤ piv) lo .snd))
        (isSet× (isProp→isSet (AllFM (Q≥ piv) hi .snd))
        (isSet× (A lo .snd) (A hi .snd)))))))

Hmap : {A B : Category.ob Fam} (b : Bag ℕ)
     → (∀ {c} → c ≺ b → ⟨ A c ⟩ → ⟨ B c ⟩)
     → ⟨ Hob A b ⟩ → ⟨ Hob B b ⟩
Hmap b f (inl e) = inl e
Hmap b f
  (inr (piv , lo , hi , loLt , hiLt , recomb , loBd , hiBd , aLo , aHi)) =
  inr ( piv , lo , hi , loLt , hiLt , recomb , loBd , hiBd
      , f loLt aLo , f hiLt aHi )

Hhom : {A B : Category.ob Fam} → Fam [ A , B ] → Fam [ Hob A , Hob B ]
Hhom {A} {B} h b = Hmap {A} {B} b (λ {c} _ → h c)

H : Functor Fam Fam
H .F-ob A          = Hob A
H .F-hom {A} {B} h = Hhom {A} {B} h
H .F-id            = funExt λ _ → funExt λ { (inl _) → refl ; (inr _) → refl }
H .F-seq _ _       = funExt λ _ → funExt λ { (inl _) → refl ; (inr _) → refl }

Hδ : LC.▷HomActionFam dir H
Hδ {A} {B} b β = Hmap {A} {B} b (λ q → LC.▷app dir β (inl q) q)

Hlc : LC.LocallyContractiveFam dir
Hlc = H , Hδ , λ h b → funExt λ { (inl _) → refl ; (inr _) → refl }

Inp Out : Category.ob Fam
Inp b = (Σ[ xs ∈ List ℕ ] (fromList xs ≡ b))
      , isSetΣ (isOfHLevelList 0 isSetℕ)
               (λ _ → isProp→isSet (FMS.trunc _ _))
Out b = (Σ[ ys ∈ List ℕ ] (Sorted ys × (fromList ys ≡ b)))
      , isSetΣ (isOfHLevelList 0 isSetℕ)
               (λ ys → isProp→isSet
                 (isProp× (isPropSorted ys) (FMS.trunc _ _)))

coalg : Fam [ Inp , H .F-ob Inp ]
coalg b ([] , e)     = inl (sym e)
coalg b (x ∷ xs , e) =
  inr ( x , fromList (lows x xs) , fromList (highs x xs)
      , cert (λ y → leq y x) , cert (λ y → not (leq y x)) , recomb
      , All→AllFM (Q≤ x) (lows x xs)
          (All-filter-sound (λ y → leq y x) (_≤ x)
            (λ y e' → leq-true y x e') xs)
      , All→AllFM (Q≥ x) (highs x xs)
          (All-filter-sound (λ y → not (leq y x)) (x ≤_)
            (λ y e' → leq-false y x (not-true (leq y x) e')) xs)
      , (lows x xs , refl)
      , (highs x xs , refl) )
  where
    lenb : lengthFM b ≡ suc (length xs)
    lenb = cong lengthFM (sym e) ∙ cong suc (lengthFM-fromList xs)
    cert : ∀ p → fromList (filterL p xs) ≺ b
    cert p = subst2 (λ m k → suc m ≤ k)
               (sym (lengthFM-fromList (filterL p xs))) (sym lenb)
               (filter-length p xs)
    recomb : b ≡ fromList (lows x xs) FMS.++ (x FMS.∷ fromList (highs x xs))
    recomb = sym e
           ∙ cong (x FMS.∷_) (partitionBag (λ y → leq y x) xs)
           ∙ bagShuffle x (fromList (lows x xs)) (fromList (highs x xs))

alg : Fam [ H .F-ob Out , Out ]
alg b (inl e) = [] , tt , sym e
alg b (inr (piv , lo , hi , _ , _ , recomb , loBd , hiBd
           , (ysL , sL , cL) , (ysR , sR , cR))) =
    ysL ++ piv ∷ ysR
  , sorted-++ ysL sL sR
      (AllFM→All (Q≤ piv) ysL
        (subst (λ c → ⟨ AllFM (Q≤ piv) c ⟩) (sym cL) loBd))
      (AllFM→All (Q≥ piv) ysR
        (subst (λ c → ⟨ AllFM (Q≥ piv) c ⟩) (sym cR) hiBd))
  , fromList-++ ysL (piv ∷ ysR)
    ∙ cong₂ FMS._++_ cL (cong (piv FMS.∷_) cR)
    ∙ sym recomb

private
  module HF = LC.HyloFam dir Hlc Inp Out coalg alg

qsort : (xs : List ℕ) → ⟨ Out (fromList xs) ⟩
qsort xs = HF.hylo .fst (fromList xs) (xs , refl)

sortList : List ℕ → List ℕ
sortList xs = qsort xs .fst

qsort-sorted : ∀ xs → Sorted (sortList xs)
qsort-sorted xs = qsort xs .snd .fst

qsort-contents : ∀ xs → fromList (sortList xs) ≡ fromList xs
qsort-contents xs = qsort xs .snd .snd

qsort-unfold : ∀ x xs
  → sortList (x ∷ xs) ≡ sortList (lows x xs) ++ x ∷ sortList (highs x xs)
qsort-unfold x xs =
  cong fst (HF.hylo-unfold (fromList (x ∷ xs)) (x ∷ xs , refl))

qsort-unique : (h : Fam [ Inp , Out ])
  → (∀ b ξ → h b ξ ≡ alg b (Hhom {Inp} {Out} h b (coalg b ξ)))
  → ∀ b ξ → h b ξ ≡ HF.hylo .fst b ξ
qsort-unique = HF.hylo-uniq-unfold

private
  _ : sortList (3 ∷ 1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
  _ = refl

  _ : sortList (5 ∷ 3 ∷ 8 ∷ 1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ []
  _ = refl

  _ : sortList (2 ∷ 2 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ 2 ∷ []
  _ = refl
