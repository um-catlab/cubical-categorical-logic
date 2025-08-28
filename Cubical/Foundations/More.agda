module Cubical.Foundations.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport

private
  variable
    ℓ : Level
    A B : Type ℓ
    x y z w v : A

rectify :
  {p q : A ≡ B}
  → (p ≡ q)
  → PathP (λ i → p i) x y
  → PathP (λ i → q i) x y
rectify {x = x}{y = y} p≡q =
  transport λ j → PathP (λ i → p≡q j i) x y

_≡[_]_ :
  (x : A)
  (p : A ≡ B)
  (y : B)
  → Type _
x ≡[ p ] y = PathP (λ i → p i) x y
