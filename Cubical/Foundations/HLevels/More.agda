module Cubical.Foundations.HLevels.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
import Cubical.Data.Nat.Base as ℕ

private
  variable
    ℓ ℓ' : Level

isPropIso : {A : Type ℓ}{B : Type ℓ'} → Iso A B → isProp B → isProp A
isPropIso f = isPropRetract (f .Iso.fun) (Iso.inv f) (Iso.ret f)

isSetIso : {A : Type ℓ}{B : Type ℓ'} → Iso A B → isSet B → isSet A
isSetIso f = isSetRetract (f .Iso.fun) (Iso.inv f) (Iso.ret f)

isOfHLevelᴰ : (n : HLevel) {A : Type ℓ}
  → isOfHLevel n A → (A → Type ℓ') → Type (ℓ-max ℓ ℓ')
isOfHLevelᴰ 0 {A = A} Acontr B =
  Σ[ b ∈ B (Acontr .fst) ]
    ({a : A} (b' : B a) →
      PathP (λ i → B (Acontr .snd a i)) b b')
isOfHLevelᴰ 1 {A = A} Aprop B =
  {a₀ a₁ : A} (b₀ : B a₀) (b₁ : B a₁) →
    PathP (λ i → B (Aprop a₀ a₁ i)) b₀ b₁
isOfHLevelᴰ (ℕ.suc (ℕ.suc n)) {A = A} Alevel B =
  {a₀ a₁ : A} (b₀ : B a₀) (b₁ : B a₁) →
    isOfHLevelᴰ (ℕ.suc n) (Alevel a₀ a₁)
      (λ p → PathP (λ i → B (p i)) b₀ b₁)

isPropᴰ : {A : Type ℓ} → isProp A → (A → Type ℓ') → Type _
isPropᴰ = isOfHLevelᴰ 1

isSetᴰ : {A : Type ℓ} → isSet A → (A → Type ℓ') → Type _
isSetᴰ = isOfHLevelᴰ 2

isOfHLevelᴰ→isOfHLevel : (n : HLevel) {A : Type ℓ}
  (Alevel : isOfHLevel n A) {B : A → Type ℓ'}
  → isOfHLevelᴰ n Alevel B
  → (a : A) → isOfHLevel n (B a)
isOfHLevelᴰ→isOfHLevel 0 Acontr {B = B} Bcontr a =
  transport (λ i → B (Acontr .snd a i)) (Bcontr .fst)
  , λ b → fromPathP (Bcontr .snd b)
isOfHLevelᴰ→isOfHLevel 1 Aprop {B = B} Bprop a b₀ b₁ =
  subst
    (λ p → PathP (λ i → B (p i)) b₀ b₁)
    (isProp→isSet Aprop a a (Aprop a a) refl)
    (Bprop b₀ b₁)
isOfHLevelᴰ→isOfHLevel (ℕ.suc (ℕ.suc n)) Alevel Blevel a b₀ b₁ =
  isOfHLevelᴰ→isOfHLevel (ℕ.suc n)
    (Alevel a a) (Blevel b₀ b₁) refl

isPropLift :
  {ℓ ℓ' : Level} →
  {A : Type ℓ} →
  isProp A → isProp (Lift ℓ' A)
isPropLift x a b = liftExt (x _ _)

isSetLift :
  {ℓ ℓ' : Level} →
  {A : Type ℓ} →
  isSet A → isSet (Lift ℓ' A)
isSetLift isSetA x y a b i =
  liftExt
    (isSetA (lower x) (lower y)
    (cong lower a) (cong lower b) i)

isGroupoidLift :
  {ℓ ℓ' : Level} →
  {A : Type ℓ} →
  isGroupoid A → isGroupoid (Lift ℓ' A)
isGroupoidLift isGroupoidA x y a b u v i j k =
  lift
  ((isGroupoidA (lower x) (lower y)) (cong lower a)
    (cong lower b) (cong (cong lower) u) (cong (cong lower) v) i j k)

isPropCod→isProp≃ :
  {a : Type ℓ}{b : Type ℓ'} →
  isProp b → isProp (a ≃ b)
isPropCod→isProp≃ isPropB =
  isPropΣ
     (isProp→ isPropB)
    λ f → isPropIsEquiv f
