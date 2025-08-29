module Cubical.Foundations.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws hiding (cong₂Funct)
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

congS₂ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}{A' : Type ℓ'}{B : Type ℓ''}{x y u v}
  (f : A → A' → B)
  (p : x ≡ y)
  (q : u ≡ v)
  → f x u ≡ f y v
congS₂ f p q = cong₂ f p q

-- Strictly better version of cong₂Funct
-- All of these are really about cong₂S not cong₂
cong₂Funct : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}{A' : Type ℓ'} {x y : A}{u v : A'} {B : Type ℓ''} (f : A → A' → B) →
        (p : x ≡ y) (q : u ≡ v) →
        cong₂ f p q ≡ cong (flip f u) p ∙ cong (f y) q
cong₂Funct {x = x} {y = y} {u = u} {v = v} f p q j i =
  hcomp (λ k → λ { (i = i0) → f x u
                  ; (i = i1) → f y (q k)
                  ; (j = i0) → f (p i) (q (i ∧ k))})
       (f (p i) u)

cong₂Funct' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}{A' : Type ℓ'} {x y : A}{u v : A'} {B : Type ℓ''} (f : A → A' → B) →
        (p : x ≡ y) (q : u ≡ v) →
        cong₂ f p q ≡ cong (f x) q ∙ cong (flip f v) p
cong₂Funct' f p q = cong₂Funct (flip f) _ _

cong₂FunctR : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}{A' : Type ℓ'} {x y : A}{u v w : A'} {B : Type ℓ''} (f : A → A' → B) →
  (p : x ≡ y) (q : u ≡ v) (r : v ≡ w) →
  cong₂ f p q ∙ cong (f y) r ≡ cong₂ f p (q ∙ r)
cong₂FunctR f p q r =
  cong₂ _∙_ (cong₂Funct f _ _) refl
  ∙ (sym $ assoc _ _ _)
  ∙ cong₂ _∙_ refl (sym $ congFunct (f _) _ _)
  ∙ (sym $ cong₂Funct f _ _)

cong₂FunctR' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}{A' : Type ℓ'} {x y : A}{u v w : A'} {B : Type ℓ''} (f : A → A' → B) →
  (p : x ≡ y) (q : u ≡ v) (r : v ≡ w) →
  cong (f x) q ∙ cong₂ f p r ≡ cong₂ f p (q ∙ r)
cong₂FunctR' f p q r =
  cong₂ _∙_ refl (cong₂Funct (flip f) _ _)
  ∙ assoc _ _ _
  ∙ cong₂ _∙_ (sym $ congFunct (f _) _ _) refl
  ∙ (sym $ cong₂Funct (flip f) _ _)

cong₂FunctL : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}{A' : Type ℓ'} {x y z : A}{u v : A'} {B : Type ℓ''} (f : A → A' → B) →
  (p : x ≡ y) (q : u ≡ v) (r : y ≡ z) →
  cong₂ f p q ∙ cong (flip f v) r ≡ cong₂ f (p ∙ r) q
cong₂FunctL f p q r = cong₂FunctR (flip f) _ _ _

cong₂FunctL' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}{A' : Type ℓ'} {x y z : A}{u v : A'} {B : Type ℓ''} (f : A → A' → B) →
  (p : x ≡ y) (q : u ≡ v) (r : y ≡ z) →
  cong (flip f u) p ∙ cong₂ f r q ≡ cong₂ f (p ∙ r) q
cong₂FunctL' f p q r = cong₂FunctR' (flip f) _ _ _

congS₂Bifunct :
  ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}{A' : Type ℓ'} {x y z : A}{u v w : A'} {B : Type ℓ''}
  (f : A → A' → B)
  (p : x ≡ y)(q : u ≡ v)
  (r : y ≡ z)(s : v ≡ w)
  → cong₂ f (p ∙ r) (q ∙ s) ≡ cong₂ f p q ∙ cong₂ f r s
congS₂Bifunct f p q r s =
  sym (cong₂FunctL f _ _ _)
  ∙ cong₂ _∙_ (sym (cong₂FunctR f _ _ _)) refl
  ∙ sym (assoc _ _ _)
  ∙ cong₂ _∙_ refl (sym (cong₂Funct' f _ _))
