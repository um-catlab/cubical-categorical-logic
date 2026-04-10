{-# OPTIONS --cubical --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Guarded.Later.Base
module Guarded.Later.Properties (k : Clock) where

open import Cubical.Foundations.Prelude

private
  variable ℓ ℓ' : Level

▹ : Type ℓ → Type ℓ
▹ A = ▹_,_ k A

isSet▹ : ∀ {ℓ} {A : Type ℓ} → ▹ (isSet A) → isSet (▹ A)
isSet▹ ▹isSetA x y x≡y x≡y' i j t = ▹isSetA t (x t) (y t) (λ i → x≡y i t) (λ i → x≡y' i t) i j

▹Π : {A : Type ℓ}{B : A → Type ℓ'} → ▹ ((a : A) → B a) → ((a : A) → ▹ (B a))
▹Π f a t = f t a

-- -- N.b.: the inverse is not definable
-- ▹Π⁻ : {A : Type ℓ}{B : A → Type ℓ'} → ((a : A) → ▹ (B a)) → ▹ ((a : A) → B a)
-- ▹Π⁻ = λ f t a → {!f a t!}

