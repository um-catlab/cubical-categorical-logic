module Cubical.Data.Sum.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sum

private
  variable
    ℓ ℓ' : Level
    A B C D E F : Type ℓ

rec-l : (A → B) → A ⊎ B → B
rec-l f = rec f (idfun _)

rec-r : (A → B) → B ⊎ A → B
rec-r f = rec (idfun _) f

map-l : (A → B) → A ⊎ C → B ⊎ C
map-l f = map f (idfun _)

map-r : (A → B) → C ⊎ A → C ⊎ B
map-r f = map (idfun _) f

map-id :
  map {ℓ}{A}{ℓ}{A}{ℓ}{B} (idfun _) (idfun _) ≡ (idfun _)
map-id i (inl x) = inl x
map-id i (inr x) = inr x

map-seq : {f : A → B}{f' : B → C}{g : D → E}{g' : E → F} →
  map (f' ∘S f) (g' ∘S g) ≡ (map f' g') ∘S (map f g)
map-seq {f = f}{f'} i (inl x) = inl (f' (f x))
map-seq {g = g}{g'} i (inr x) = inr (g' (g x))
