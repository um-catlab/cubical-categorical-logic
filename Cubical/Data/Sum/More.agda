module Cubical.Data.Sum.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
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

open Iso
ΣDistR⊎Iso :
  ∀ {B : A → Type ℓ}{C : A → Type ℓ'}
  → Iso (Σ[ a ∈ A ] (B a ⊎ C a))
        ((Σ[ a ∈ A ] B a) ⊎ (Σ[ a ∈ A ] C a))
ΣDistR⊎Iso .fun (a , inl b) = inl (a , b)
ΣDistR⊎Iso .fun (a , inr c) = inr (a , c)
ΣDistR⊎Iso .inv (inl (a , b)) = a , (inl b)
ΣDistR⊎Iso .inv (inr (a , c)) = a , (inr c)
ΣDistR⊎Iso .sec (inl (a , b)) = refl
ΣDistR⊎Iso .sec (inr (a , c)) = refl
ΣDistR⊎Iso .ret (a , inl b) = refl
ΣDistR⊎Iso .ret (a , inr c) = refl
