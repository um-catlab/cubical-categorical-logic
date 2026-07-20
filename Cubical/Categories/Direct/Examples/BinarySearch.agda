{-# OPTIONS --lossy-unification #-}
-- Intrinsically correct binary search returning the index, as a hylomorphism.
module Cubical.Categories.Direct.Examples.BinarySearch where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Data.Maybe using (Maybe ; just ; nothing ; map-Maybe)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive
  using (_≤_ ; _<_ ; isProp≤ ; ≤-trans ; <-weaken ; ¬m<m ; <→≢
        ; Trichotomy ; lt ; eq ; gt ; _≟_)
open import Cubical.Data.List
  using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.List.More
open import Cubical.Data.Fin using (Fin ; toℕ)

open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no ; isProp¬)
open import Cubical.Relation.Nullary.More using (isSetDec)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor using (Functor)
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.ListByLength using (ListDirect)
import Cubical.Categories.Direct.LocallyContractive as LC

open Functor

private
  dir = ListDirect ℕ isSetℕ

open DirectNotation dir using (_≺_ ; isProp≺)

Fam : Category _ _
Fam = LC.Fam dir

open Ordered _≤_ isProp≤ ≤-trans

≤<-trans : ∀ {a b c} → a ≤ b → b < c → a < c
≤<-trans {a} {b} {c} a≤b b<c = ≤-trans {suc a} {suc b} {c} a≤b b<c

half : ℕ → ℕ
half zero          = zero
half (suc zero)    = zero
half (suc (suc n)) = suc (half n)

half< : ∀ m → half (suc m) < suc m
half< zero          = tt
half< (suc zero)    = tt
half< (suc (suc m)) = <-weaken (half< m)

module _ (q : ℕ) where

  Member : List ℕ → Type
  Member xs = q ∈ xs

  MemIff : List ℕ → List ℕ → Type
  MemIff xs ys = (Member xs → Member ys) × (Member ys → Member xs)

  isSetMemIff : ∀ xs ys → isSet (MemIff xs ys)
  isSetMemIff xs ys =
    isSet× (isSetΠ λ _ → isSet∈ isSetℕ ys) (isSetΠ λ _ → isSet∈ isSetℕ xs)

  Hob : Category.ob Fam → Category.ob Fam
  Hob A xs =
      ( (¬ Member xs)
      ⊎ ( Member xs
        ⊎ (Σ[ ys ∈ List ℕ ] ((ys ≺ xs) × MemIff xs ys × ⟨ A ys ⟩)) ) )
    , isSet⊎ (isProp→isSet (isProp¬ (Member xs)))
        (isSet⊎ (isSet∈ isSetℕ xs)
          (isSetΣ (isOfHLevelList 0 isSetℕ) λ ys →
            isSet× (isProp→isSet (isProp≺ ys xs))
            (isSet× (isSetMemIff xs ys) (A ys .snd))))

  Hmap : {A B : Category.ob Fam} (xs : List ℕ)
       → (∀ {ys} → ys ≺ xs → ⟨ A ys ⟩ → ⟨ B ys ⟩)
       → ⟨ Hob A xs ⟩ → ⟨ Hob B xs ⟩
  Hmap xs f (inl ¬m)      = inl ¬m
  Hmap xs f (inr (inl m)) = inr (inl m)
  Hmap xs f (inr (inr (ys , ys≺ , iff , a))) =
    inr (inr (ys , ys≺ , iff , f ys≺ a))

  Hhom : {A B : Category.ob Fam} → Fam [ A , B ] → Fam [ Hob A , Hob B ]
  Hhom {A} {B} h xs = Hmap {A} {B} xs (λ {ys} _ → h ys)

  H : Functor Fam Fam
  H .F-ob A          = Hob A
  H .F-hom {A} {B} h = Hhom {A} {B} h
  H .F-id            = funExt λ _ → funExt
    λ { (inl _) → refl ; (inr (inl _)) → refl ; (inr (inr _)) → refl }
  H .F-seq _ _       = funExt λ _ → funExt
    λ { (inl _) → refl ; (inr (inl _)) → refl ; (inr (inr _)) → refl }

  Hδ : LC.▷HomActionFam dir H
  Hδ {A} {B} xs β = Hmap {A} {B} xs (λ q' → LC.▷app dir β (inl q') q')

  Hlc : LC.LocallyContractiveFam dir
  Hlc = H , Hδ , λ h xs → funExt
    λ { (inl _) → refl ; (inr (inl _)) → refl ; (inr (inr _)) → refl }

  Inp Out : Category.ob Fam
  Inp xs = Sorted xs , isProp→isSet (isPropSorted xs)
  Out xs = Dec (Member xs) , isSetDec (isSet∈ isSetℕ xs)

  alg : Fam [ H .F-ob Out , Out ]
  alg xs (inl ¬m)                               = no ¬m
  alg xs (inr (inl m))                          = yes m
  alg xs (inr (inr (ys , _ , (to , from) , d))) = decMap d
    where
      decMap : Dec (Member ys) → Dec (Member xs)
      decMap (yes b) = yes (from b)
      decMap (no ¬b) = no (λ a → ¬b (to a))

  coalg : Fam [ Inp , H .F-ob Inp ]
  coalg []        s = inl (λ ())
  coalg (x ∷ xs') s = go (q ≟ mid)
    where
      full = x ∷ xs'
      k    = half (length full)
      lo   = take k full
      mid  = lookupD 0 full k
      hi   = drop (suc k) full

      k<len : k < length full
      k<len = half< (length xs')

      recomb : full ≡ lo ++ mid ∷ hi
      recomb = sym (take-lookup-drop 0 k full k<len)

      split : All (_≤ mid) lo × Sorted lo × All (mid ≤_) hi × Sorted hi
      split = Sorted-split lo (subst Sorted recomb s)

      loB = split .fst
      slo = split .snd .fst
      hiB = split .snd .snd .fst
      shi = split .snd .snd .snd

      lo≺ : lo ≺ full
      lo≺ = ≤-trans (length-take-≤ k full) (half< (length xs'))
      hi≺ : hi ≺ full
      hi≺ = length-drop-≤ k xs'

      fromLo : Member lo → Member full
      fromLo q∈lo = subst (q ∈_) (sym recomb) (∈-++ˡ q∈lo)
      fromHi : Member hi → Member full
      fromHi q∈hi = subst (q ∈_) (sym recomb) (∈-++ʳ lo (inr q∈hi))

      go : Trichotomy q mid → ⟨ Hob Inp full ⟩
      go (eq q≡mid) =
        inr (inl (subst (q ∈_) (sym recomb) (∈-++ʳ lo (inl q≡mid))))
      go (lt q<mid) = inr (inr (lo , lo≺ , (toLo , fromLo) , slo))
        where
          ¬q∈hi : ¬ (q ∈ hi)
          ¬q∈hi q∈hi = ¬m<m (≤<-trans (All-∈ hiB q∈hi) q<mid)
          toLo : Member full → Member lo
          toLo m with ∈-++⁻ lo (subst (q ∈_) recomb m)
          ... | inl q∈lo        = q∈lo
          ... | inr (inl q≡mid) = ⊥.rec (<→≢ q<mid q≡mid)
          ... | inr (inr q∈hi)  = ⊥.rec (¬q∈hi q∈hi)
      go (gt mid<q) = inr (inr (hi , hi≺ , (toHi , fromHi) , shi))
        where
          ¬q∈lo : ¬ (q ∈ lo)
          ¬q∈lo q∈lo = ¬m<m (≤<-trans (All-∈ loB q∈lo) mid<q)
          toHi : Member full → Member hi
          toHi m with ∈-++⁻ lo (subst (q ∈_) recomb m)
          ... | inl q∈lo        = ⊥.rec (¬q∈lo q∈lo)
          ... | inr (inl q≡mid) = ⊥.rec (<→≢ mid<q (sym q≡mid))
          ... | inr (inr q∈hi)  = q∈hi

  private
    module HF = LC.HyloFam dir Hlc Inp Out coalg alg

  member? : ∀ xs → Sorted xs → Dec (Member xs)
  member? = HF.hylo .fst

  search : ∀ xs → Sorted xs → Maybe (Fin (length xs))
  search xs s with member? xs s
  ... | yes m = just (∈→Fin m)
  ... | no  _ = nothing

private
  s123 : Sorted (1 ∷ 2 ∷ 3 ∷ [])
  s123 = (tt , tt , tt) , (tt , tt) , (tt , tt)

  _ : map-Maybe toℕ (search 1 (1 ∷ 2 ∷ 3 ∷ []) s123) ≡ just 0
  _ = refl

  _ : map-Maybe toℕ (search 2 (1 ∷ 2 ∷ 3 ∷ []) s123) ≡ just 1
  _ = refl

  _ : map-Maybe toℕ (search 3 (1 ∷ 2 ∷ 3 ∷ []) s123) ≡ just 2
  _ = refl

  _ : search 5 (1 ∷ 2 ∷ 3 ∷ []) s123 ≡ nothing
  _ = refl

  _ : search 0 (1 ∷ 2 ∷ 3 ∷ []) s123 ≡ nothing
  _ = refl
