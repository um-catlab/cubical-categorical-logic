{-

  Path is nice because reasons.

  Eq is nice because definitional JRefl

  What if best of both worlds? But only if we have an hSet

-}
module Cubical.HITs.PathEq where

open import Cubical.Foundations.More
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq
open import Cubical.HITs.Join as Join
open import Cubical.HITs.Join.More as Join hiding (elim; elimProp)
private
  variable
    ℓ ℓ' ℓ'' : Level

PathEq : {X : Type ℓ} (x : X) (x' : X) → Type ℓ
PathEq {X = X} x x' = join (x ≡ x') (x Eq.≡ x')

module _ {X : Type ℓ} (isSetX : isSet X) where
  private
    variable x x' x'' : X
  isPropPathEq : isProp (PathEq {X = X} x x')
  isPropPathEq = isPropJoin (isSetX _ _) (Eq.isSet→isSetEq isSetX)

  symPE : PathEq x x' → PathEq x' x
  symPE = Join.elimProp (λ _ → isPropPathEq)
    (λ pf → inl (sym pf))
    λ pf → inr (Eq.sym pf)

  PathEq→Path : (p : PathEq x x') → Path X x x'
  PathEq→Path = Join.elimProp (λ _ → isSetX _ _)
    (λ p → p)
    Eq.eqToPath

  PathEq→Eq : (p : PathEq x x') → x Eq.≡ x'
  PathEq→Eq = Join.elimProp (λ _ → Eq.isSet→isSetEq isSetX)
    Eq.pathToEq
    λ y → y

  PathEq→Path→PathEq : (p : PathEq x x') → PathEq x x'
  PathEq→Path→PathEq p = inl (PathEq→Path p)

  -- elimEq : {M : (p : PathEq x x') → Type ℓ''}
  --   → (∀ p → M (inr p))
  --   → (∀ p → M p)
  -- elimEq {M = M} Meq = Join.elim
  --   (λ path → subst M (sym (push path (Eq.pathToEq path))) (Meq (Eq.pathToEq path)))
  --   Meq
  --   λ { path eq →
  --     {!!}
  --     ▷ ({!!} ≡⟨ {!!} ⟩ Meq eq ∎)
  --   }

  elimPropPath : {M : (p : PathEq x x') → Type ℓ''}
    → (∀ p → isProp (M p))
    → (∀ p → M (inl p))
    → ∀ p → M p
  elimPropPath {M = M} isPropM Mpath = Join.elimProp
    isPropM
    Mpath
    (λ eq → subst M (push (Eq.eqToPath eq) eq) (Mpath (Eq.eqToPath eq)))

  elimPropEq : {M : (p : PathEq x x') → Type ℓ''}
    → (∀ p → isProp (M p))
    → (∀ p → M (inr p))
    → ∀ p → M p
  elimPropEq {M = M} isPropM Meq = Join.elimProp
    isPropM
    (λ p → subst M (sym $ push p (Eq.pathToEq p)) (Meq (Eq.pathToEq p)))
    Meq

  elimPropBoth : {M : (p : PathEq x x') → Type ℓ''}
    → (∀ p → isProp (M p))
    → (∀ p → M (inl p))
    → (∀ p → M (inr p))
    → ∀ p → M p
  elimPropBoth {M = M} isPropM Mp Meq =
    Join.elimProp isPropM Mp Meq

  epSubst : ∀ {x x' : X} (B : X → Type ℓ') → PathEq x x' → B x → B x'
  epSubst {x = x} {x'} B = Join.elim (subst B) (Eq.transport B)
    (λ { p Eq.refl → funExt (λ b → sym $ Prectify (subst-filler (λ z → z) (λ i → B (p i)) (Eq.transport B Eq.refl b))) })
    where
      open hSetReasoning (X , isSetX) B


module _ {X : Type ℓ}{Y : Type ℓ'} {x x' : X}{y y' : Y}
  (isSetX : isSet X) (isSetY : isSet Y)
  (px : PathEq x x') (py : PathEq y y')
  where

  PathEq× : PathEq (x , y) (x' , y')
  PathEq× = elimPropBoth isSetX
    (λ px → isPropPE×)
    (λ x≡x' → elimPropBoth isSetY (λ _ → isPropPE×)
      (λ y≡y' → inl (≡-× x≡x' y≡y'))
      (λ where Eq.refl → inl (≡-× x≡x' refl)) py)
    (λ {Eq.refl → elimPropBoth isSetY (λ _ → isPropPE×)
      (λ y≡y' → inl (≡-× refl y≡y'))
      (λ where Eq.refl → inr Eq.refl)
      py})
    px
    where
    isPropPE× : isProp (PathEq (x , y) (x' , y'))
    isPropPE× = isPropPathEq (isSet× isSetX isSetY)
