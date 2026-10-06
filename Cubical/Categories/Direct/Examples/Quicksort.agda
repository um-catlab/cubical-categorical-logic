{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Direct.Examples.Quicksort where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (⟨_⟩)

open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; false≢true ; true≢false ; isSetBool)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.Nat.Order.Recursive using (_≤_)
import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.List.More
  using (All ; module Ordered ; filterL ; All-filter-sound ; Ilv-filter)
open import Cubical.Data.Empty as ⊥ using (⊥)
import Cubical.HITs.FiniteMultiset as FMS
open import Cubical.HITs.FiniteMultiset.More
  using (fromList ; fromList-++ ; bagShuffle ; Ilv→fromList ; AllFM ; All→AllFM ; AllFM→All)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Instances.BinProduct using (_,F_)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive
  using (module Hylo ; isLocallyContractive)
open import Cubical.Categories.Enriched.Enrichment.Instances.FullSubcategory
  using (ToFullSubcategory-Enr ; ToFullSubcategory-LC)
open import Cubical.Categories.Displayed.Instances.FunctorAlgebras using (InitialAlgebra)
open import Cubical.Categories.Displayed.Instances.FunctorCoalgebras using (TerminalCoalgebra)

open import Cubical.Categories.Direct.Instances.Monoid using (Factor ; factorDirect)
open import Cubical.Categories.Direct.Instances.Monoid.Instances using (BagGM)

private
  GM = BagGM (ℕ , isSetℕ)

open import Cubical.Categories.Direct.Guarded.Monoid GM
  using (Fam ; ⌈_⌉ ; NonNullable ; ⌈⌉-NN ; NonNullable-⊗ˡ)
open import Cubical.Categories.Direct.Guarded.Monoid.Factor GM
  using (⊗F ; ⊗-LCˡ ; ⊗-LCʳ)
open import Cubical.Categories.Direct.Guarded.Presheaf (factorDirect GM) using (pshGuarded)
open import Cubical.Categories.Direct.Guarded.Family (factorDirect GM)
  using (ΣFam ; LC-Σ ; Restrict ; Restrict-Enr)
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive.Bifunctor pshGuarded
  using (LC-const ; LCˡ-precomp ; LCʳ-precomp)
open import Cubical.Categories.Enriched.Enrichment.Instances.Family.Limits (Factor GM) ℓ-zero
  using (famEnrichment)
open import Cubical.Categories.Direct.ContractiveCompleteness.Family (factorDirect GM)
  using (famInitialAlgebra ; famTerminalCoalgebra)

Bag : Type
Bag = FMS.FMSet ℕ

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

Below Above : ℕ → Category.ob Fam
Below piv (_ , b) = AllFM (Q≤ piv) b .fst , isProp→isSet (AllFM (Q≤ piv) b .snd)
Above piv (_ , b) = AllFM (Q≥ piv) b .fst , isProp→isSet (AllFM (Q≥ piv) b .snd)

private
  ⊤ : Category.ob Fam → Type
  ⊤ _ = Unit

  Fam⊤ Fam⁺ : Category _ _
  Fam⊤ = FullSubcategory Fam ⊤
  Fam⁺ = FullSubcategory Fam NonNullable

module _ (piv : ℕ) where
  private
    pivNN : NonNullable ⌈ piv FMS.∷ FMS.[] ⌉
    pivNN = ⌈⌉-NN (piv FMS.∷ FMS.[]) tt

  Lo : Functor Fam Fam⊤
  Lo = ToFullSubcategory Fam Fam ⊤ (Restrict (Below piv)) λ _ → tt

  Pt : Functor Fam Fam⁺
  Pt = ToFullSubcategory Fam Fam NonNullable (Constant Fam Fam ⌈ piv FMS.∷ FMS.[] ⌉) λ _ → pivNN

  Ab : Functor Fam Fam⊤
  Ab = ToFullSubcategory Fam Fam ⊤ (Restrict (Above piv)) λ _ → tt

  Hi : Functor Fam Fam⁺
  Hi = ToFullSubcategory Fam Fam NonNullable (⊗F NonNullable ⊤ ∘F (Pt ,F Ab))
    λ X → NonNullable-⊗ˡ _ pivNN

  Split : Functor Fam Fam
  Split = ⊗F ⊤ NonNullable ∘F (Lo ,F Hi)

  Split-LC : isLocallyContractive pshGuarded famEnrichment famEnrichment Split
  Split-LC = LCˡ-precomp {Φ = ⊗F ⊤ NonNullable} {F₁ = Lo} {F₂ = Hi} ⊗-LCˡ
    (ToFullSubcategory-Enr {Q = ⊤} {F = Restrict (Below piv)} (λ _ → tt) (Restrict-Enr (Below piv)))
    (ToFullSubcategory-LC {Q = NonNullable} {F = ⊗F NonNullable ⊤ ∘F (Pt ,F Ab)}
      (λ X → NonNullable-⊗ˡ _ pivNN) pshGuarded
      (LCʳ-precomp {Φ = ⊗F NonNullable ⊤} {F₁ = Pt} {F₂ = Ab} ⊗-LCʳ
        (ToFullSubcategory-LC {Q = NonNullable} {F = Constant Fam Fam ⌈ piv FMS.∷ FMS.[] ⌉}
          (λ _ → pivNN) pshGuarded
          (LC-const famEnrichment famEnrichment ⌈ piv FMS.∷ FMS.[] ⌉))
        (ToFullSubcategory-Enr {Q = ⊤} {F = Restrict (Above piv)} (λ _ → tt)
          (Restrict-Enr (Above piv)))))

Branch : Bool → Functor Fam Fam
Branch false = Constant Fam Fam ⌈ FMS.[] ⌉
Branch true  = ΣFam (ℕ , isSetℕ) Split

H : Functor Fam Fam
H = ΣFam (Bool , isSetBool) Branch

H-LC : isLocallyContractive pshGuarded famEnrichment famEnrichment H
H-LC = LC-Σ (Bool , isSetBool) Branch λ
  { false → LC-const famEnrichment famEnrichment ⌈ FMS.[] ⌉
  ; true  → LC-Σ (ℕ , isSetℕ) Split Split-LC }

μH : InitialAlgebra H
μH = famInitialAlgebra H H-LC

νH : TerminalCoalgebra H
νH = famTerminalCoalgebra H H-LC

Inp Out : Category.ob Fam
Inp (_ , b) = (Σ[ xs ∈ List ℕ ] (fromList xs ≡ b))
            , isSetΣ (isOfHLevelList 0 isSetℕ) (λ _ → isProp→isSet (FMS.trunc _ _))
Out (_ , b) = (Σ[ ys ∈ List ℕ ] (Sorted ys × (fromList ys ≡ b)))
            , isSetΣ (isOfHLevelList 0 isSetℕ)
                (λ ys → isProp→isSet (isProp× (isPropSorted ys) (FMS.trunc _ _)))

coalg : Fam [ Inp , H ⟅ Inp ⟆ ]
coalg (_ , b) ([] , e) = false , sym e
coalg (_ , b) (x ∷ xs , e) =
  true , x
  , fromList (lows x xs) , x FMS.∷ fromList (highs x xs)
  , sym (cong (x FMS.∷_) (Ilv→fromList xs (Ilv-filter (λ y → leq y x) xs))
         ∙ bagShuffle x (fromList (lows x xs)) (fromList (highs x xs))) ∙ e
  , ((lows x xs , refl) , All→AllFM (Q≤ x) (lows x xs)
        (All-filter-sound (λ y → leq y x) (_≤ x) (λ y e' → leq-true y x e') xs))
  , ( x FMS.∷ FMS.[] , fromList (highs x xs) , refl , refl
    , ((highs x xs , refl) , All→AllFM (Q≥ x) (highs x xs)
        (All-filter-sound (λ y → not (leq y x)) (x ≤_)
          (λ y e' → leq-false y x (not-true (leq y x) e')) xs)))

alg : Fam [ H ⟅ Out ⟆ , Out ]
alg (_ , b) (false , p) = [] , tt , sym p
alg (_ , b) (true , piv , lo , v , s , ((ysL , sL , cL) , loB)
                    , (u' , hi , s' , pu , ((ysR , sR , cR) , hiB))) =
    ysL ++ piv ∷ ysR
  , sorted-++ ysL sL sR
      (AllFM→All (Q≤ piv) ysL (subst (λ c → ⟨ AllFM (Q≤ piv) c ⟩) (sym cL) loB))
      (AllFM→All (Q≥ piv) ysR (subst (λ c → ⟨ AllFM (Q≥ piv) c ⟩) (sym cR) hiB))
  , fromList-++ ysL (piv ∷ ysR)
    ∙ cong₂ FMS._++_ cL (cong (piv FMS.∷_) cR ∙ cong (FMS._++ hi) (sym pu) ∙ s')
    ∙ s

private
  module HY = Hylo pshGuarded {F = H} H-LC {X = Inp} {B = Out} coalg alg

qsort : (xs : List ℕ) → ⟨ Out (tt , fromList xs) ⟩
qsort xs = HY.hylo (tt , fromList xs) (xs , refl)

sortList : List ℕ → List ℕ
sortList xs = qsort xs .fst

qsort-sorted : ∀ xs → Sorted (sortList xs)
qsort-sorted xs = qsort xs .snd .fst

qsort-contents : ∀ xs → fromList (sortList xs) ≡ fromList xs
qsort-contents xs = qsort xs .snd .snd

private
  _ : sortList (3 ∷ 1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ []
  _ = refl

  _ : sortList (5 ∷ 3 ∷ 8 ∷ 1 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 5 ∷ 8 ∷ []
  _ = refl

  _ : sortList (2 ∷ 2 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ 2 ∷ []
  _ = refl
