-- TODO: upstream urgently
module Cubical.HITs.Join.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
open import Cubical.HITs.Join
private
  variable ℓ ℓ' ℓ'' : Level

isProp' : (X : Type ℓ) → Type _
isProp' X = X → isContr X

isProp'→isProp : {X : Type ℓ} → isProp' X → isProp X
isProp'→isProp isProp'X x = isContr→isProp (isProp'X x) x

module _ {ℓ ℓ'}{X : Type ℓ}{Y : Type ℓ'} where
  elim : ∀ {Z : join X Y → Type ℓ''}
    → (l : ∀ x → Z (inl x))
    → (r : ∀ y → Z (inr y))
    → (p : ∀ x y → PathP (λ i → Z (push x y i)) (l x) (r y))
    → ∀ j → Z j
  elim l r p (inl x) = l x
  elim l r p (inr x) = r x
  elim l r p (push a b i) = p a b i
  {-# INLINE elim #-}

  elimProp : ∀ {Z : join X Y → Type ℓ''} → (isPropZ : ∀ j → isProp (Z j))
    → (l : ∀ x → Z (inl x))
    → (r : ∀ y → Z (inr y))
    → ∀ j → Z j
  elimProp isPropZ l r =
    elim l r
      (λ x y → isProp→PathP (λ i → isPropZ (push x y i)) (l x) (r y))

  join-rec : ∀ {Z : Type ℓ''} → (l : X → Z) → (r : Y → Z)
    → (l≡r : ∀ x y → l x ≡ r y)
    → join X Y → Z
  join-rec l r l≡r = elim l r l≡r

  isContrJoinL : isContr X → isContr (join X Y)
  isContrJoinL isContrX .fst = inl (isContrX .fst)
  isContrJoinL isContrX .snd = elim
    (λ x i → inl (isContrX .snd x i))
    (λ y → push (isContrX .fst) y)
    (λ x y i j → hcomp (λ where
      --        x  x
      -- j↑ k→  x  x0
      k (i = i0) → inl (isContrX .snd x (~ k ∨ j))
      --        y  y
      -- j↑ k→  x  x0
      k (i = i1) → push (isContrX .snd x (~ k)) y j
      --       x0 x0
      -- k↑ i→ x  x
      k (j = i0) → inl (isContrX .snd x (~ k))
      --       x y
      -- k↑ i→ x y
      k (j = i1) → push x y i
    )
      --       x y
      -- j↑ i→ x x
    (push x y (i ∧ j)))

  isContrJoinR : isContr Y → isContr (join X Y)
  isContrJoinR isContrY .fst = inr (isContrY .fst)
  isContrJoinR isContrY .snd (inl x) = sym $ push x _
  isContrJoinR isContrY .snd (inr y) i = inr (isContrY .snd y i)
  -- goal
  -- --    x  - push  - y
  --       | push⁻      | inr (y0≡ y j)
  -- j↑ i→ y0 ========= y0
  isContrJoinR (y0 , y0≡) .snd (push x y i) j = hcomp (λ where
    k (i = i0) → push x (y0≡ y (~ k)) (~ j)
    k (i = i1) → inr (y0≡ y (~ k ∨ j))
    k (j = i0) → inr (y0≡ y (~ k))
    k (j = i1) → push x y i)
    -- base
    -- x y
    -- y y
    -- when
      -- i=0: push x y (~ j)
      -- i=1: inr y
      -- j=0: inr y
      -- j=1: inr y
    (push x y (i ∨ (~ j)))

  isPropJoin : isProp X → isProp Y → isProp (join X Y)
  isPropJoin isPropX isPropY = isProp'→isProp (elimProp
    (λ j → isPropIsContr)
      (λ x → isContrJoinL (inhProp→isContr x isPropX))
      (λ y → isContrJoinR (inhProp→isContr y isPropY)))
