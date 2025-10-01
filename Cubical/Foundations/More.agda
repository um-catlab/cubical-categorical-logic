module Cubical.Foundations.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws hiding (cong₂Funct)
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
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

-- Reasoning about a dependent type that is indexed by an hSet
module hSetReasoning (A : hSet ℓ) (P : ⟨ A ⟩ → Type ℓ') where
  _P≡[_]_ : ∀ {a b : ⟨ A ⟩} (p : P a) → (a≡b : a ≡ b) → (q : P b) → Type _
  p P≡[ a≡b ] q = p ≡[ cong P a≡b ] q
  private
    variable
      a b c : ⟨ A ⟩
      p q r : P a
      pth qth : a ≡ b
  ≡in :
    p P≡[ pth ] q
    → Path (Σ ⟨ A ⟩ P) (a , p) (b , q)
  ≡in e = ΣPathP $ _ , e

  ≡out :
    (e : Path (Σ ⟨ A ⟩ P) (a , p) (b , q))
    → p P≡[ fst $ PathPΣ e ] q
  ≡out e = snd $ PathPΣ e

  reind : (a ≡ b) → P a → P b
  reind e p = subst P e p

  reind-filler :
    ∀ (e : a ≡ b)
    → Path (Σ ⟨ A ⟩ P) (a , p) (b , reind e p)
  reind-filler e = ΣPathP (e , (subst-filler P e _))

  -- This is the only part that requires the hSet stuff. Everything else is completely generic
  Prectify :
    ∀ {e e' : a ≡ b}
    → p P≡[ e ] q
    → p P≡[ e' ] q
  Prectify {p = p}{q = q} = subst (p P≡[_] q) (A .snd _ _ _ _)

ΣPathPᴰ :
  ∀ {A : Type ℓ}{P : A → Type ℓ'}
  {B : Type ℓ''}{Q : B → Type ℓ'''}
  {x y}
  → Path (Σ A P) (x .fst .fst , x .snd .fst) (y .fst .fst , y .snd .fst)
  → Path (Σ B Q) (x .fst .snd , x .snd .snd) (y .fst .snd , y .snd .snd)
  → Path (Σ (A × B) (λ ab → P (ab .fst) × Q (ab .snd))) x y
ΣPathPᴰ ap≡ bq≡ i = ((ap≡ i .fst) , (bq≡ i .fst)) , ((ap≡ i .snd) , (bq≡ i .snd))

PathPᴰΣ :
  ∀ {A : Type ℓ}{P : A → Type ℓ'}
  {B : Type ℓ''}{Q : B → Type ℓ'''}
  {x y}
  → Path (Σ (A × B) (λ ab → P (ab .fst) × Q (ab .snd))) x y
  → ( Path (Σ A P) (x .fst .fst , x .snd .fst) (y .fst .fst , y .snd .fst)
    × Path (Σ B Q) (x .fst .snd , x .snd .snd) (y .fst .snd , y .snd .snd))
PathPᴰΣ abpq≡ .fst i = (abpq≡ i .fst .fst) , (abpq≡ i .snd .fst)
PathPᴰΣ abpq≡ .snd i = (abpq≡ i .fst .snd) , (abpq≡ i .snd .snd)

ΣPathPSnd :
  ∀ {A : Type ℓ}{B : A → Type ℓ'}{C : (a : A)(b : B a) → Type ℓ''} {x y}
  → (ab≡ : Path (Σ A B) (x .fst , x .snd .fst) (y .fst , y .snd .fst))
  → PathP (λ i → C (ab≡ i .fst) (ab≡ i .snd)) (x .snd .snd) (y .snd .snd)
  → Path (Σ A (λ a → Σ (B a) (C a))) x y
ΣPathPSnd ab≡ c≡ = ΣPathP ((cong fst ab≡) , (ΣPathP ((cong snd ab≡) , c≡)))

×≡Snd :
  ∀ {A : Type ℓ}{B : A → Type ℓ'}{C : A → Type ℓ''} {x y}
  → (ab≡ : Path (Σ A B) (x .fst , x .snd .fst) (y .fst , y .snd .fst))
  → PathP (λ i → C (ab≡ i .fst)) (x .snd .snd) (y .snd .snd)
  → Path (Σ A (λ a → (B a) × (C a))) x y
×≡Snd ab≡ c≡ = ΣPathP ((cong fst ab≡) , (ΣPathP ((cong snd ab≡) , c≡)))

×≡Snd-hSet :
  ∀ {A : Type ℓ}{B : A → Type ℓ'}{C : A → Type ℓ''} {x y}
  → (isSet A)
  → (Path (Σ A B) (x .fst , x .snd .fst) (y .fst , y .snd .fst))
  → (Path (Σ A C) (x .fst , x .snd .snd) (y .fst , y .snd .snd))
  → Path (Σ A (λ a → B a × C a)) x y
×≡Snd-hSet {C = C} isSetA ab≡ ac≡ = ΣPathP ((cong fst ab≡) , (ΣPathP ((λ i → ab≡ i .snd) , (rectify (cong (cong C)
  (isSetA _ _ _ _)) (λ i → ac≡ i .snd)))))

PathPΣSnd : ∀ {A : Type ℓ}{B : A → Type ℓ'}{C : (a : A)(b : B a) → Type ℓ''} {x y}
  → Path (Σ A (λ a → Σ (B a) (C a))) x y
  → Σ[ ab≡ ∈ Path (Σ A B) (x .fst , x .snd .fst) (y .fst , y .snd .fst) ]
    PathP (λ i → C (ab≡ i .fst) (ab≡ i .snd)) (x .snd .snd) (y .snd .snd)
PathPΣSnd abc≡ .fst i = (abc≡ i .fst) , (abc≡ i .snd .fst)
PathPΣSnd abc≡ .snd i = abc≡ i .snd .snd

≡×Snd : ∀ {A : Type ℓ}{B : A → Type ℓ'}{C : A → Type ℓ''} {x y}
  → Path (Σ A (λ a → B a × C a)) x y
  → Path (Σ A B) (x .fst , x .snd .fst) (y .fst , y .snd .fst)
    × Path (Σ A C) (x .fst , x .snd .snd) (y .fst , y .snd .snd)
≡×Snd abc≡ .fst i = abc≡ i .fst , abc≡ i .snd .fst
≡×Snd abc≡ .snd i = abc≡ i .fst , abc≡ i .snd .snd

congSndSnd :
  ∀ {A : Type ℓ}{B : A → Type ℓ'}{C : (a : A)(b : B a) → Type ℓ''}{x y}
  → (abc≡ : Path (Σ A (λ a → Σ (B a) (C a))) x y)
  → PathP (λ i → C (abc≡ i .fst) (abc≡ i .snd .fst)) (x .snd .snd) (y .snd .snd)
congSndSnd abc≡ = λ i → abc≡ i .snd .snd

-- TODO: name
change-base :
  ∀ {A : Type ℓ}{B : Type ℓ'}{C : B → Type ℓ''}
  (f : A → B)
  {x y}
  → isSet B
  → Path A (x .fst) (y .fst)
  → Path (Σ B C) (f (x .fst) , x .snd) (f (y .fst) , y .snd)
  → Path (Σ A (λ a → C (f a))) x y
change-base {C = C} f isSetB a≡ bc≡ =
  ΣPathP (a≡ , (rectify (cong (cong C) (isSetB _ _ _ _)) λ i → bc≡ i .snd))

change-base⁻ :
  ∀ {A : Type ℓ}{B : Type ℓ'}{C : B → Type ℓ''}
  (f : A → B)
  {x y}
  → Path (Σ A (λ a → C (f a))) x y
  → Path (Σ B C) (f (x .fst) , x .snd) (f (y .fst) , y .snd)
change-base⁻ f ac≡ = ΣPathP ((cong f (cong fst ac≡)) , λ i → ac≡ i .snd)

funExt₂⁻ : {B : A → Type ℓ} {C : (a : A) → B a → I → Type ℓ'}
  {f : (x : A) → (y : B x) → C x y i0}
  {g : (x : A) → (y : B x) → C x y i1}
  → PathP (λ i → (x : A) → (y : B x) → C x y i) f g
  → ((x : A) → (y : B x) → PathP (C x y) (f x y) (g x y))
funExt₂⁻ eq x y i = eq i x y
