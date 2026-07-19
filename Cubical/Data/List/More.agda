-- `All`, membership, and (order-parametrised) `Sorted` predicates on lists,
-- with the append/split lemmas shared by the sorting/searching
-- hylomorphism examples.
module Cubical.Data.List.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Empty as ⊥ using (⊥ ; isProp⊥)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order.Recursive
  using (_≤_ ; _<_ ; ≤-refl ; ≤-trans ; n≤k+n)
open import Cubical.Data.List
  using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)

private
  variable
    ℓ : Level

  ≤-suc : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-suc {zero}          _  = tt
  ≤-suc {suc m} {zero}  le = ⊥.rec le
  ≤-suc {suc m} {suc n} le = ≤-suc {m} {n} le

-- total indexing with a default for the out-of-range / empty case
lookupD : {A : Type ℓ} → A → List A → ℕ → A
lookupD d []       _       = d
lookupD d (x ∷ xs) zero    = x
lookupD d (x ∷ xs) (suc n) = lookupD d xs n

filterL : {A : Type ℓ} → (A → Bool) → List A → List A
filterL p []       = []
filterL p (y ∷ ys) = if p y then y ∷ filterL p ys else filterL p ys

filter-length : {A : Type ℓ} (p : A → Bool) (xs : List A)
              → length (filterL p xs) ≤ length xs
filter-length p []       = tt
filter-length p (y ∷ ys) = go (p y)
  where
    go : ∀ b → length (if b then y ∷ filterL p ys else filterL p ys)
             ≤ suc (length ys)
    go true  = filter-length p ys
    go false = ≤-suc {length (filterL p ys)} {length ys} (filter-length p ys)

module _ {A : Type} where
  All : (A → Type) → List A → Type
  All P []       = Unit
  All P (x ∷ xs) = P x × All P xs

  isPropAll : ∀ {P} → (∀ z → isProp (P z)) → ∀ xs → isProp (All P xs)
  isPropAll pr []       = isPropUnit
  isPropAll pr (x ∷ xs) = isProp× (pr x) (isPropAll pr xs)

  All-++ : ∀ {P} as {bs} → All P as → All P bs → All P (as ++ bs)
  All-++ []       _          qb = qb
  All-++ (a ∷ as) (qa , qas) qb = qa , All-++ as qas qb

  All-++⁻ : ∀ {P} as {bs} → All P (as ++ bs) → All P as × All P bs
  All-++⁻ []       a        = tt , a
  All-++⁻ (x ∷ as) (px , a) with All-++⁻ as a
  ... | la , lb = (px , la) , lb

  All-mono : ∀ {P Q : A → Type} (f : ∀ z → P z → Q z) xs → All P xs → All Q xs
  All-mono f []       _          = tt
  All-mono f (x ∷ xs) (qx , qxs) = f x qx , All-mono f xs qxs

  All-filter-sound : ∀ (p : A → Bool) (Q : A → Type)
    → (∀ y → p y ≡ true → Q y) → ∀ xs → All Q (filterL p xs)
  All-filter-sound p Q sound []       = tt
  All-filter-sound p Q sound (y ∷ ys) = go (p y) refl
    where
      go : ∀ b → p y ≡ b
         → All Q (if b then y ∷ filterL p ys else filterL p ys)
      go true  e = sound y e , All-filter-sound p Q sound ys
      go false e = All-filter-sound p Q sound ys

  _∈_ : A → List A → Type
  q ∈ []       = ⊥
  q ∈ (x ∷ xs) = (q ≡ x) ⊎ (q ∈ xs)

  isSet∈ : isSet A → ∀ {q} xs → isSet (q ∈ xs)
  isSet∈ sA []       = isProp→isSet isProp⊥
  isSet∈ sA (x ∷ xs) = isSet⊎ (isProp→isSet (sA _ _)) (isSet∈ sA xs)

  ∈→Fin : ∀ {q xs} → q ∈ xs → Fin (length xs)
  ∈→Fin {xs = x ∷ xs} (inl _) = fzero
  ∈→Fin {xs = x ∷ xs} (inr m) = fsuc (∈→Fin m)

  ∈-++ˡ : ∀ {q as bs} → q ∈ as → q ∈ (as ++ bs)
  ∈-++ˡ {as = x ∷ as} (inl p) = inl p
  ∈-++ˡ {as = x ∷ as} (inr m) = inr (∈-++ˡ m)

  ∈-++ʳ : ∀ {q} as {bs} → q ∈ bs → q ∈ (as ++ bs)
  ∈-++ʳ []       m = m
  ∈-++ʳ (x ∷ as) m = inr (∈-++ʳ as m)

  ∈-++⁻ : ∀ {q} as {bs} → q ∈ (as ++ bs) → (q ∈ as) ⊎ (q ∈ bs)
  ∈-++⁻ []       m       = inr m
  ∈-++⁻ (x ∷ as) (inl p) = inl (inl p)
  ∈-++⁻ (x ∷ as) (inr m) = Sum.map inr (λ r → r) (∈-++⁻ as m)

  All-∈ : ∀ {P q xs} → All P xs → q ∈ xs → P q
  All-∈ {P} {xs = x ∷ xs} (px , _)  (inl p) = subst P (sym p) px
  All-∈     {xs = x ∷ xs} (_  , ps) (inr m) = All-∈ ps m

  length-take-≤ : ∀ k (xs : List A) → length (take k xs) ≤ k
  length-take-≤ zero    xs       = tt
  length-take-≤ (suc k) []       = tt
  length-take-≤ (suc k) (x ∷ xs) = length-take-≤ k xs

  length-drop-≤ : ∀ k (xs : List A) → length (drop k xs) ≤ length xs
  length-drop-≤ zero    xs       = ≤-refl (length xs)
  length-drop-≤ (suc k) []       = tt
  length-drop-≤ (suc k) (x ∷ xs) =
    ≤-trans {length (drop k xs)} {length xs} {suc (length xs)}
      (length-drop-≤ k xs) (n≤k+n {k = 1} (length xs))

  take-lookup-drop : ∀ (d : A) k xs → k < length xs
    → take k xs ++ (lookupD d xs k ∷ drop (suc k) xs) ≡ xs
  take-lookup-drop d k       []       hyp = ⊥.rec hyp
  take-lookup-drop d zero    (x ∷ xs) hyp = refl
  take-lookup-drop d (suc k) (x ∷ xs) hyp =
    cong (x ∷_) (take-lookup-drop d k xs hyp)

module Ordered {A : Type} (_≤_ : A → A → Type)
               (isProp≤ : ∀ {a b} → isProp (a ≤ b))
               (≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c) where
  Sorted : List A → Type
  Sorted []       = Unit
  Sorted (x ∷ xs) = All (x ≤_) xs × Sorted xs

  isPropSorted : ∀ xs → isProp (Sorted xs)
  isPropSorted []       = isPropUnit
  isPropSorted (x ∷ xs) =
    isProp× (isPropAll (λ _ → isProp≤) xs) (isPropSorted xs)

  Sorted-split : ∀ lo {mid hi} → Sorted (lo ++ mid ∷ hi)
    → All (_≤ mid) lo × Sorted lo × All (mid ≤_) hi × Sorted hi
  Sorted-split []       (midB , shi) = tt , tt , midB , shi
  Sorted-split (y ∷ lo) (yAll , srest)
    with All-++⁻ lo yAll | Sorted-split lo srest
  ... | yAll-lo , (y≤mid , _) | loB , slo , hiB , shi =
        (y≤mid , loB) , (yAll-lo , slo) , hiB , shi

  sorted-++ : ∀ l {piv r} → Sorted l → Sorted r
    → All (_≤ piv) l → All (piv ≤_) r → Sorted (l ++ piv ∷ r)
  sorted-++ []      _          sr _          ar = ar , sr
  sorted-++ (y ∷ l) {piv} {r} (ybd , sl) sr (y≤p , al) ar =
      All-++ l ybd (y≤p , All-mono (λ _ p≤z → ≤-trans y≤p p≤z) r ar)
    , sorted-++ l sl sr al ar
