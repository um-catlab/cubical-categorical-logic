{-

  WORKED NORMAL FORMS for Multicategory.STLC.

  Small examples exercising the normal-form machinery of
  Multicategory.NbE: a context, a term, its η-long normal form, and the
  proof that the normal form embeds back to the term.  Each `-nf` proof
  is the equation of the theory that the η-expansion is FOR, so these
  double as a readable statement of what normalization does here.

  WHAT THESE ARE NOT.  `norm` proves that a normal form EXISTS; it does
  not compute one.  Its conclusion is

      ∥ Σ[ n ∈ NfA Γ A ] ⌜ n ⌝nf ≡ t ∥₁

  and the truncation goes all the way down: the logical predicate at
  the base type is itself `R ι Γ t = ∥ Σ[ n ∈ NfA Γ ι ] ⌜ n ⌝nf ≡ t ∥₁`.
  That is deliberate, and NbE.agda's header says why -- a prop-valued
  predicate makes the fundamental theorem cheap, because the syntax's
  fourteen path constructors are all discharged by `ElimPropA` and not a
  single equation of the theory has to be met in the model.  The price
  is exactly that nothing computes out.

  So the normal forms below are supplied BY HAND and VERIFIED, rather
  than produced by running the normalizer.  `norm-*` at the bottom
  records separately that `norm` does prove existence for each of them.
  Getting an actual normalizer would need a set-valued predicate, hence
  meeting each equation of the theory in the model.

-}
{-# OPTIONS --lossy-unification #-}
module Multicategory.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Multicategory.STLC
open import Multicategory.NbE

-- ------------------------------------------------------------------
-- Contexts with a single variable, at three different types.

one : (A : TyA) → CtxA
one A = (Unit , isSetUnit) , (λ _ → A)

Γι Γ⊤ Γ× Γ⇒ : CtxA
Γι = one ι
Γ⊤ = one ⊤ᴬ
Γ× = one (ι ×ᴬ ι)
Γ⇒ = one (ι ⇒ᴬ ι)

-- ------------------------------------------------------------------
-- 1.  A VARIABLE AT THE BASE TYPE is already normal.

x : Term Γι ι
x = varA tt

x-nf : ⌜ neNf (varNe tt) ⌝nf ≡ x
x-nf = refl

-- ------------------------------------------------------------------
-- 2.  AT THE UNIT TYPE everything normalises to `ttNf`, including a
--     variable.  The proof IS the η rule.

y : Term Γ⊤ ⊤ᴬ
y = varA tt

y-nf : ⌜ ttNf ⌝nf ≡ y
y-nf = sym (⊤ηA y)

-- ------------------------------------------------------------------
-- 3.  AT A PRODUCT a variable η-EXPANDS: its normal form is the pair
--     of its two projections, each of which is neutral.

p : Term Γ× (ι ×ᴬ ι)
p = varA tt

p-nf : ⌜ pairNf (neNf (fstNe (varNe tt))) (neNf (sndNe (varNe tt))) ⌝nf
       ≡ p
p-nf = ×ηA p

-- ------------------------------------------------------------------
-- 4.  AT A FUNCTION TYPE a variable η-expands to a lambda whose body
--     applies the weakened variable to the bound one -- the η-long
--     form.  Note the normal form is genuinely bigger than the term.

f : Term Γ⇒ (ι ⇒ᴬ ι)
f = varA tt

-- `⇒ηA` states the expansion with the variable WEAKENED as a
-- substitution, `f ⟨ inl ⟩A`; the normal form has the weakened
-- variable itself, so one clone law bridges them.
f-nf : ⌜ lamNf (neNf (appNe (varNe (inl tt)) (neNf (varNe (inr tt))))) ⌝nf
       ≡ f
f-nf =
  sym (cong (λ z → lamA (appA z (varA (inr tt))))
        (⟨⟩varA tt (λ j → varA (inl j))))
  ∙ ⇒ηA f

-- ------------------------------------------------------------------
-- 5.  BETA.  The identity function applied to a variable is that
--     variable.  `⇒βA` is forded: it takes the substitution the
--     redex contracts to.

idfn : Term Γι (ι ⇒ᴬ ι)
idfn = lamA (varA (inr tt))

-- `⇒βA` is FORDED on the substitution: rather than forming the
-- singleton substitution itself, it takes any `f` together with
-- witnesses that `f` is the identity on the old variables and sends
-- the bound one to `u`.  Here both witnesses are `refl`.
beta : appA idfn x ≡ x
beta =
  ⇒βA (varA (inr tt)) x (Sum.elim varA (λ _ → x))
      (λ i → refl) refl
  ∙ ⟨⟩varA (inr tt) (Sum.elim varA (λ _ → x))

-- so the redex has the same normal form as the variable
beta-nf : ⌜ neNf (varNe tt) ⌝nf ≡ appA idfn x
beta-nf = sym beta

-- ------------------------------------------------------------------
-- 6.  `norm` PROVES EXISTENCE for each of the above.  These typecheck
--     but cannot be projected out of -- see the header.

norm-x : ∥ Σ[ n ∈ NfA Γι ι ] ⌜ n ⌝nf ≡ x ∥₁
norm-x = norm x

norm-y : ∥ Σ[ n ∈ NfA Γ⊤ ⊤ᴬ ] ⌜ n ⌝nf ≡ y ∥₁
norm-y = norm y

norm-p : ∥ Σ[ n ∈ NfA Γ× (ι ×ᴬ ι) ] ⌜ n ⌝nf ≡ p ∥₁
norm-p = norm p

norm-f : ∥ Σ[ n ∈ NfA Γ⇒ (ι ⇒ᴬ ι) ] ⌜ n ⌝nf ≡ f ∥₁
norm-f = norm f

norm-beta : ∥ Σ[ n ∈ NfA Γι ι ] ⌜ n ⌝nf ≡ appA idfn x ∥₁
norm-beta = norm (appA idfn x)
