{-# OPTIONS --prop #-}
module Cubical.Prop.NatOrder where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Base

open import Cubical.Prop.Bottom
open import Cubical.Prop.Top

_≤_ : ℕ → ℕ → Prop
zero ≤ n = ⊤
suc m ≤ zero = ⊥
suc m ≤ suc n = m ≤ n

≤-refl : ∀ n → n ≤ n
≤-refl zero = tt
≤-refl (suc n) = ≤-refl n

≤-trans : ∀ l m n → l ≤ m → m ≤ n → l ≤ n
≤-trans zero m n _ _ = tt
≤-trans (suc l) (suc m) (suc n) l≤m m≤n = ≤-trans l m n l≤m m≤n

