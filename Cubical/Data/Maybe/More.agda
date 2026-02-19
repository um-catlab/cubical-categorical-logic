module Cubical.Data.Maybe.More where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Relation.Binary.Preorder

open import Cubical.Data.Empty renaming (elim to ⊥elim)
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

private
  variable
    ℓ : Level

isSetMaybe : {A : hSet ℓ} → isSet (Maybe ⟨ A ⟩)
isSetMaybe {A = A} = isOfHLevelMaybe 0 (A .snd)

map-Maybe-seq : {A B C : Type ℓ}{f : A → B}{g : B → C} → (x : Maybe A) →
  map-Maybe (λ x₂ → g (f x₂)) x ≡ map-Maybe g (map-Maybe f x)
map-Maybe-seq nothing = refl
map-Maybe-seq (just x) = refl

-- not MaybeRel _≡_, this is the information ordering
_≤_ : {A : Type ℓ} → Maybe A → Maybe A → Type ℓ
nothing ≤ n = Unit*
just x ≤ nothing = ⊥*
just x ≤ just y = x ≡ y

≤-isProp : {A : hSet ℓ}{m n : Maybe ⟨ A ⟩} → isProp (_≤_ {A = ⟨ A ⟩} m n )
≤-isProp {m = nothing} {nothing} = isPropUnit*
≤-isProp {m = nothing} {just x} = isPropUnit*
≤-isProp {m = just x} {nothing} ()
≤-isProp {A = A} {just x} {just y} p q = A .snd x y p q

≤-refl : {A : Type ℓ}{m : Maybe A} → m ≤ m
≤-refl {m = nothing} = tt*
≤-refl {m = just x} = refl

≤-trans : {A : Type ℓ}{m n p : Maybe A} →
  m ≤ n → n ≤ p → m ≤ p
≤-trans {m = nothing} {n} {p} _ _ = tt*
≤-trans {m = just x} {nothing} {p} ()
≤-trans {m = just x} {just y} {nothing} _ ()
≤-trans {m = just x} {just y} {just z} p q = p ∙ q

maybePreorder : (X : hSet ℓ) → Preorder ℓ ℓ
maybePreorder X =
  Maybe ⟨ X ⟩ ,
  preorderstr
    _≤_
    (ispreorder
      (λ _ _ → ≤-isProp {A = X})
      (λ _ → ≤-refl)
      (λ _ _ _ → ≤-trans))

≡-to-≤m  : {A : Type ℓ}{m n : Maybe A} → m ≡ n → m ≤ n
≡-to-≤m  {m = nothing} {n} _ = tt*
≡-to-≤m  {m = just x} {nothing} p =
  ⊥elim {A = λ _ → (just x) ≤ nothing}(¬nothing≡just (sym p))
≡-to-≤m  {m = just x} {just x₁} p = just-inj _ _ p

inversion : {A : Type ℓ}{a : A}{n : Maybe A} →
  (just a) ≤ n → Σ A λ a' → (n ≡ just a') × (a ≡ a' )
inversion {n = just x} p = x , refl , p

mono-map : {A B : Type ℓ}{m n : Maybe A}{f : A → B} →
  m ≤ n → (map-Maybe f m) ≤ (map-Maybe f n)
mono-map {m = nothing} {y} p = tt*
mono-map {m = just x} {just y}{f} p = cong f p

mono-f-eq : {A B : Type ℓ}{m : Maybe A}{f g : A → B} →
  f ≡ g → (map-Maybe f m) ≤ (map-Maybe g m)
mono-f-eq {m = nothing} p = tt*
mono-f-eq {m = just x} p = funExt⁻ p _

mono-map-comp : {A B C : Type ℓ}{m : Maybe A}
  {f : A → B}{g : B → C}→
  (map-Maybe (g ∘S f) m) ≤ (map-Maybe g (map-Maybe f m))
mono-map-comp  {m = nothing} = tt*
mono-map-comp  {m = just x} = refl
