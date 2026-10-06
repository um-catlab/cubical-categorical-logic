module Cubical.Data.List.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; if_then_else_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-suc)
open import Cubical.Data.Nat.Order.Recursive using (_≤_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)

private
  variable
    ℓ : Level

  ≤-suc : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-suc {zero}          _  = tt
  ≤-suc {suc m} {zero}  le = ⊥.rec le
  ≤-suc {suc m} {suc n} le = ≤-suc {m} {n} le

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

  sorted-++ : ∀ l {piv r} → Sorted l → Sorted r
    → All (_≤ piv) l → All (piv ≤_) r → Sorted (l ++ piv ∷ r)
  sorted-++ []      _          sr _          ar = ar , sr
  sorted-++ (y ∷ l) {piv} {r} (ybd , sl) sr (y≤p , al) ar =
      All-++ l ybd (y≤p , All-mono (λ _ p≤z → ≤-trans y≤p p≤z) r ar)
    , sorted-++ l sl sr al ar

module _ {A : Type ℓ} where
  Ilv : List A → List A → List A → Type ℓ
  Ilv u v []      = (u ≡ []) × (v ≡ [])
  Ilv u v (x ∷ w) = (Σ[ u' ∈ List A ] (u ≡ x ∷ u') × Ilv u' v w)
                  ⊎ (Σ[ v' ∈ List A ] (v ≡ x ∷ v') × Ilv u v' w)

  Ilv-filter : ∀ (p : A → Bool) xs
    → Ilv (filterL p xs) (filterL (λ y → not (p y)) xs) xs
  Ilv-filter p []       = refl , refl
  Ilv-filter p (y ∷ ys) = go (p y)
    where
      go : ∀ b → Ilv (if b then y ∷ filterL p ys else filterL p ys)
                     (if not b then y ∷ filterL (λ y' → not (p y')) ys
                               else filterL (λ y' → not (p y')) ys)
                     (y ∷ ys)
      go true  = inl (_ , refl , Ilv-filter p ys)
      go false = inr (_ , refl , Ilv-filter p ys)
