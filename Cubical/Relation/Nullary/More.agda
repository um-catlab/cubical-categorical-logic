-- Closure properties of Dec missing from Cubical.Relation.Nullary
module Cubical.Relation.Nullary.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr ; isSet⊎)
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Relation.Nullary using (¬_ ; Dec ; yes ; no ; isProp¬)

private
  variable
    ℓ ℓ' : Level

isSetDec : {A : Type ℓ} → isSet A → isSet (Dec A)
isSetDec {A = A} sA =
  isOfHLevelRetract 2 f g fg (isSet⊎ sA (isProp→isSet (isProp¬ A)))
  where
    f : Dec A → A ⊎ (¬ A)
    f (yes a) = inl a
    f (no ¬a) = inr ¬a
    g : A ⊎ (¬ A) → Dec A
    g (inl a)  = yes a
    g (inr ¬a) = no ¬a
    fg : ∀ d → g (f d) ≡ d
    fg (yes a) = refl
    fg (no ¬a) = refl

Dec× : {A : Type ℓ} {B : Type ℓ'} → Dec A → Dec B → Dec (A × B)
Dec× (yes a) (yes b) = yes (a , b)
Dec× (no ¬a) _       = no (λ (a , _) → ¬a a)
Dec× _       (no ¬b) = no (λ (_ , b) → ¬b b)

Dec¬ : {A : Type ℓ} → Dec A → Dec (¬ A)
Dec¬ (yes a) = no (λ ¬a → ¬a a)
Dec¬ (no ¬a) = yes ¬a

Dec→ : {A : Type ℓ} {B : Type ℓ'} → Dec A → Dec B → Dec (A → B)
Dec→ (yes a) (yes b) = yes (λ _ → b)
Dec→ (yes a) (no ¬b) = no (λ f → ¬b (f a))
Dec→ (no ¬a) _       = yes (λ a → ⊥.rec (¬a a))
