{-

  Normalization by evaluation for the sum-free fragment.

  The model is a Kripke logical predicate over the category of
  renamings — a presheaf on renamings, in the usual NbE sense — and the
  two directions are reflect (neutrals satisfy the predicate) and reify
  (whatever satisfies it has a normal form).  The predicate is
  PROP-VALUED, which is what makes the fundamental theorem cheap: the
  syntax's fourteen path constructors are all discharged by ElimPropA,
  so not a single equation of the theory has to be checked in the
  model.  The price is that the normal form is extracted only up to
  propositional truncation.

-}
module Multicategory.NbE where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PT

open import Multicategory.STLC

-- TyA is a set, by decidable equality
private
  Code : TyA → TyA → Type
  Code ι ι = Unit
  Code ⊤ᴬ ⊤ᴬ = Unit
  Code (A ×ᴬ B) (A' ×ᴬ B') = Code A A' × Code B B'
  Code (A ⇒ᴬ B) (A' ⇒ᴬ B') = Code A A' × Code B B'
  Code _ _ = ⊥

  reflCode : (A : TyA) → Code A A
  reflCode ι = tt
  reflCode ⊤ᴬ = tt
  reflCode (A ×ᴬ B) = reflCode A , reflCode B
  reflCode (A ⇒ᴬ B) = reflCode A , reflCode B

  decode : (A B : TyA) → Code A B → A ≡ B
  decode ι ι _ = refl
  decode ⊤ᴬ ⊤ᴬ _ = refl
  decode (A ×ᴬ B) (A' ×ᴬ B') (c , d) =
    cong₂ _×ᴬ_ (decode A A' c) (decode B B' d)
  decode (A ⇒ᴬ B) (A' ⇒ᴬ B') (c , d) =
    cong₂ _⇒ᴬ_ (decode A A' c) (decode B B' d)

  codeDec : (A B : TyA) → Dec (Code A B)
  codeDec ι ι = yes tt
  codeDec ι ⊤ᴬ = no (λ ())
  codeDec ι (_ ×ᴬ _) = no (λ ())
  codeDec ι (_ ⇒ᴬ _) = no (λ ())
  codeDec ⊤ᴬ ι = no (λ ())
  codeDec ⊤ᴬ ⊤ᴬ = yes tt
  codeDec ⊤ᴬ (_ ×ᴬ _) = no (λ ())
  codeDec ⊤ᴬ (_ ⇒ᴬ _) = no (λ ())
  codeDec (_ ×ᴬ _) ι = no (λ ())
  codeDec (_ ×ᴬ _) ⊤ᴬ = no (λ ())
  codeDec (_ ×ᴬ _) (_ ⇒ᴬ _) = no (λ ())
  codeDec (_ ⇒ᴬ _) ι = no (λ ())
  codeDec (_ ⇒ᴬ _) ⊤ᴬ = no (λ ())
  codeDec (_ ⇒ᴬ _) (_ ×ᴬ _) = no (λ ())
  codeDec (A ×ᴬ B) (A' ×ᴬ B') = decRec
    (λ c → decRec (λ d → yes (c , d)) (λ ¬d → no (λ e → ¬d (e .snd)))
      (codeDec B B'))
    (λ ¬c → no (λ e → ¬c (e .fst))) (codeDec A A')
  codeDec (A ⇒ᴬ B) (A' ⇒ᴬ B') = decRec
    (λ c → decRec (λ d → yes (c , d)) (λ ¬d → no (λ e → ¬d (e .snd)))
      (codeDec B B'))
    (λ ¬c → no (λ e → ¬c (e .fst))) (codeDec A A')

  encode : (A B : TyA) → A ≡ B → Code A B
  encode A B p = subst (Code A) p (reflCode A)

isSetTyA : isSet TyA
isSetTyA = Discrete→isSet (λ A B → decRec
  (λ c → yes (decode A B c)) (λ ¬c → no (λ p → ¬c (encode A B p)))
  (codeDec A B))

-- contexts and renamings, with the typing condition forded
CtxA : Type₁
CtxA = Σ[ I ∈ hSet ℓ-zero ] (⟨ I ⟩ → TyA)

Vars : CtxA → Type
Vars Γ = ⟨ Γ .fst ⟩

Typing : (Γ : CtxA) → Vars Γ → TyA
Typing Γ = Γ .snd

record Rename (Γ Δ : CtxA) : Type where
  field
    vars : Vars Γ → Vars Δ
    typed : (i : Vars Γ) {A : TyA}
      → Typing Δ (vars i) ≡ A → Typing Γ i ≡ A

open Rename

typedOb : {Γ Δ : CtxA} (ρ : Rename Γ Δ) (i : Vars Γ)
  → Typing Γ i ≡ Typing Δ (ρ .vars i)
typedOb ρ i = ρ .typed i refl

idRen : {Γ : CtxA} → Rename Γ Γ
idRen .vars i = i
idRen .typed i p = p

_⨟_ : {Γ Δ Θ : CtxA} → Rename Γ Δ → Rename Δ Θ → Rename Γ Θ
(ρ ⨟ σ) .vars i = σ .vars (ρ .vars i)
(ρ ⨟ σ) .typed i p = ρ .typed i (σ .typed (ρ .vars i) p)

-- context extension, and a renaming lifted under a binder
_,,ᶜ_ : CtxA → TyA → CtxA
(Γ ,,ᶜ A) .fst = (Vars Γ ⊎ Unit) , isSet⊎ (str (Γ .fst)) isSetUnit
(Γ ,,ᶜ A) .snd = Typing Γ ,,ᴬ A

wkᶜ : {Γ : CtxA} {A : TyA} → Rename Γ (Γ ,,ᶜ A)
wkᶜ .vars i = inl i
wkᶜ .typed i p = p

_↑_ : {Γ Δ : CtxA} → Rename Γ Δ → (A : TyA)
  → Rename (Γ ,,ᶜ A) (Δ ,,ᶜ A)
(ρ ↑ A) .vars = Sum.elim (λ i → inl (ρ .vars i)) (λ _ → inr tt)
(ρ ↑ A) .typed (inl i) p = ρ .typed i p
(ρ ↑ A) .typed (inr _) p = p

-- terms in a context, and weakening
Term : CtxA → TyA → Type₁
Term Γ A = TmA (Vars Γ) (Typing Γ) A

wkVar : {Γ Δ : CtxA} (ρ : Rename Γ Δ) (i : Vars Γ)
  → Term Δ (Typing Γ i)
wkVar {Γ} {Δ} ρ i =
  subst (Term Δ) (sym (typedOb ρ i)) (varA (ρ .vars i))

wk : {Γ Δ : CtxA} {A : TyA} (ρ : Rename Γ Δ) → Term Γ A → Term Δ A
wk ρ t = t ⟨ wkVar ρ ⟩A

wkVar-id : {Γ : CtxA} (i : Vars Γ) → wkVar (idRen {Γ}) i ≡ varA i
wkVar-id {Γ} i = substRefl {B = Term Γ} (varA i)

wk-id : {Γ : CtxA} {A : TyA} (t : Term Γ A) → wk (idRen {Γ}) t ≡ t
wk-id {Γ} t = cong (t ⟨_⟩A) (funExt (wkVar-id {Γ})) ∙ ⟨⟩idA t

wkVar-⨟ : {Γ Δ Θ : CtxA} (ρ : Rename Γ Δ) (σ : Rename Δ Θ) (i : Vars Γ)
  → wkVar (ρ ⨟ σ) i ≡ (wkVar ρ i ⟨ wkVar σ ⟩A)
wkVar-⨟ {Γ} {Δ} {Θ} ρ σ i =
  cong (λ p → subst (Term Θ) p (varA (σ .vars (ρ .vars i))))
    (isSetTyA _ _ _ (sym (typedOb σ (ρ .vars i)) ∙ sym (typedOb ρ i)))
  ∙ substComposite (Term Θ) (sym (typedOb σ (ρ .vars i)))
      (sym (typedOb ρ i)) (varA (σ .vars (ρ .vars i)))
  ∙ cong (subst (Term Θ) (sym (typedOb ρ i)))
      (sym (⟨⟩varA (ρ .vars i) (wkVar σ)))
  ∙ substCommSlice (Term Δ) (Term Θ) (λ _ t → t ⟨ wkVar σ ⟩A)
      (sym (typedOb ρ i)) (varA (ρ .vars i))

wk-⨟ : {Γ Δ Θ : CtxA} {A : TyA}
  (ρ : Rename Γ Δ) (σ : Rename Δ Θ) (t : Term Γ A)
  → wk (ρ ⨟ σ) t ≡ wk σ (wk ρ t)
wk-⨟ ρ σ t =
  cong (t ⟨_⟩A) (funExt (wkVar-⨟ ρ σ))
  ∙ sym (⟨⟩⟨⟩A t (wkVar ρ) (wkVar σ))

-- lifting a weakening is the substitution the ford of lam-natA wants
wkVar-↑ : {Γ Δ : CtxA} {A : TyA} (ρ : Rename Γ Δ) (i : Vars Γ)
  → wkVar (ρ ↑ A) (inl i) ≡ (wkVar ρ i ⟨ (λ j → varA (inl j)) ⟩A)
wkVar-↑ {Γ} {Δ} {A} ρ i =
  cong (subst (Term (Δ ,,ᶜ A)) (sym (typedOb ρ i)))
    (sym (⟨⟩varA (ρ .vars i) (λ j → varA (inl j))))
  ∙ substCommSlice (Term Δ) (Term (Δ ,,ᶜ A))
      (λ _ t → t ⟨ (λ j → varA (inl j)) ⟩A)
      (sym (typedOb ρ i)) (varA (ρ .vars i))

wkVar-↑r : {Γ Δ : CtxA} {A : TyA} (ρ : Rename Γ Δ)
  → wkVar (ρ ↑ A) (inr tt) ≡ varA (inr tt)
wkVar-↑r {Γ} {Δ} {A} ρ = substRefl {B = Term (Δ ,,ᶜ A)} (varA (inr tt))

-- neutrals and normal forms.  A neutral is a normal form only at the
-- base type: ⊤ᴬ, ×ᴬ and ⇒ᴬ all have η rules, so this is the η-long
-- discipline.
data NeA : (Γ : CtxA) (A : TyA) → Type₁
data NfA : (Γ : CtxA) (A : TyA) → Type₁

data NeA where
  varNe : {Γ : CtxA} (i : Vars Γ) → NeA Γ (Typing Γ i)
  fstNe : {Γ : CtxA} {A B : TyA} → NeA Γ (A ×ᴬ B) → NeA Γ A
  sndNe : {Γ : CtxA} {A B : TyA} → NeA Γ (A ×ᴬ B) → NeA Γ B
  appNe : {Γ : CtxA} {A B : TyA}
    → NeA Γ (A ⇒ᴬ B) → NfA Γ A → NeA Γ B

data NfA where
  neNf : {Γ : CtxA} → NeA Γ ι → NfA Γ ι
  ttNf : {Γ : CtxA} → NfA Γ ⊤ᴬ
  pairNf : {Γ : CtxA} {A B : TyA} → NfA Γ A → NfA Γ B → NfA Γ (A ×ᴬ B)
  lamNf : {Γ : CtxA} {A B : TyA} → NfA (Γ ,,ᶜ A) B → NfA Γ (A ⇒ᴬ B)

⌜_⌝ne : {Γ : CtxA} {A : TyA} → NeA Γ A → Term Γ A
⌜_⌝nf : {Γ : CtxA} {A : TyA} → NfA Γ A → Term Γ A
⌜ varNe i ⌝ne = varA i
⌜ fstNe n ⌝ne = fstA ⌜ n ⌝ne
⌜ sndNe n ⌝ne = sndA ⌜ n ⌝ne
⌜ appNe n m ⌝ne = appA ⌜ n ⌝ne ⌜ m ⌝nf
⌜ neNf n ⌝nf = ⌜ n ⌝ne
⌜ ttNf ⌝nf = ttA
⌜ pairNf m n ⌝nf = pairA ⌜ m ⌝nf ⌜ n ⌝nf
⌜ lamNf n ⌝nf = lamA ⌜ n ⌝nf

-- weakening of neutrals and normals, and its compatibility with the
-- embedding.  The only transport is at a variable.
wkNe : {Γ Δ : CtxA} {A : TyA} → Rename Γ Δ → NeA Γ A → NeA Δ A
wkNf : {Γ Δ : CtxA} {A : TyA} → Rename Γ Δ → NfA Γ A → NfA Δ A
wkNe {Γ} {Δ} ρ (varNe i) =
  subst (NeA Δ) (sym (typedOb ρ i)) (varNe (ρ .vars i))
wkNe ρ (fstNe n) = fstNe (wkNe ρ n)
wkNe ρ (sndNe n) = sndNe (wkNe ρ n)
wkNe ρ (appNe n m) = appNe (wkNe ρ n) (wkNf ρ m)
wkNf ρ (neNf n) = neNf (wkNe ρ n)
wkNf ρ ttNf = ttNf
wkNf ρ (pairNf m n) = pairNf (wkNf ρ m) (wkNf ρ n)
wkNf {Γ} {Δ} ρ (lamNf {A = A} n) = lamNf (wkNf (ρ ↑ A) n)

wkNe-⌜⌝ : {Γ Δ : CtxA} {A : TyA} (ρ : Rename Γ Δ) (n : NeA Γ A)
  → ⌜_⌝ne {Δ} {A} (wkNe ρ n) ≡ wk ρ (⌜_⌝ne {Γ} {A} n)
wkNf-⌜⌝ : {Γ Δ : CtxA} {A : TyA} (ρ : Rename Γ Δ) (n : NfA Γ A)
  → ⌜_⌝nf {Δ} {A} (wkNf ρ n) ≡ wk ρ (⌜_⌝nf {Γ} {A} n)
wkNe-⌜⌝ {Γ} {Δ} ρ (varNe i) =
  sym (substCommSlice (NeA Δ) (Term Δ) (λ _ n → ⌜ n ⌝ne)
        (sym (typedOb ρ i)) (varNe (ρ .vars i)))
  ∙ sym (⟨⟩varA i (wkVar ρ))
wkNe-⌜⌝ ρ (fstNe n) =
  cong fstA (wkNe-⌜⌝ ρ n) ∙ sym (fst-natA ⌜ n ⌝ne (wkVar ρ))
wkNe-⌜⌝ ρ (sndNe n) =
  cong sndA (wkNe-⌜⌝ ρ n) ∙ sym (snd-natA ⌜ n ⌝ne (wkVar ρ))
wkNe-⌜⌝ ρ (appNe n m) =
  cong₂ appA (wkNe-⌜⌝ ρ n) (wkNf-⌜⌝ ρ m)
  ∙ sym (app-natA ⌜ n ⌝ne ⌜ m ⌝nf (wkVar ρ))
wkNf-⌜⌝ ρ (neNf n) = wkNe-⌜⌝ ρ n
wkNf-⌜⌝ ρ ttNf = sym (⊤ηA (ttA ⟨ wkVar ρ ⟩A))
wkNf-⌜⌝ ρ (pairNf m n) =
  cong₂ pairA (wkNf-⌜⌝ ρ m) (wkNf-⌜⌝ ρ n)
  ∙ sym (pair-natA ⌜ m ⌝nf ⌜ n ⌝nf (wkVar ρ))
wkNf-⌜⌝ {Γ} {Δ} ρ (lamNf {A = A} n) =
  cong lamA (wkNf-⌜⌝ (ρ ↑ A) n)
  ∙ sym (lam-natA ⌜ n ⌝nf (wkVar ρ) (wkVar (ρ ↑ A))
          (wkVar-↑ ρ) (wkVar-↑r ρ))

-- THE KRIPKE LOGICAL PREDICATE.  Prop-valued, so the fundamental
-- theorem below is an ElimPropA and none of the syntax's fourteen path
-- constructors has to be checked.
R : (A : TyA) (Γ : CtxA) → Term Γ A → Type₁
R ι Γ t = ∥ Σ[ n ∈ NfA Γ ι ] ⌜ n ⌝nf ≡ t ∥₁
R ⊤ᴬ Γ t = Unit*
R (A ×ᴬ B) Γ t = R A Γ (fstA t) × R B Γ (sndA t)
R (A ⇒ᴬ B) Γ t =
  (Δ : CtxA) (ρ : Rename Γ Δ) (u : Term Δ A)
  → R A Δ u → R B Δ (appA (wk ρ t) u)

isPropR : (A : TyA) (Γ : CtxA) (t : Term Γ A) → isProp (R A Γ t)
isPropR ι Γ t = squash₁
isPropR ⊤ᴬ Γ t = isPropUnit*
isPropR (A ×ᴬ B) Γ t =
  isProp× (isPropR A Γ (fstA t)) (isPropR B Γ (sndA t))
isPropR (A ⇒ᴬ B) Γ t =
  isPropΠ (λ Δ → isPropΠ (λ ρ → isPropΠ (λ u → isPropΠ (λ _ →
    isPropR B Δ (appA (wk ρ t) u)))))

-- the predicate is a presheaf on renamings
monR : (A : TyA) {Γ Δ : CtxA} (ρ : Rename Γ Δ) (t : Term Γ A)
  → R A Γ t → R A Δ (wk ρ t)
monR ι ρ t =
  PT.map (λ (n , p) → wkNf ρ n , wkNf-⌜⌝ ρ n ∙ cong (wk ρ) p)
monR ⊤ᴬ ρ t _ = tt*
monR (A ×ᴬ B) {Γ} {Δ} ρ t (ra , rb) =
  subst (R A Δ) (fst-natA t (wkVar ρ)) (monR A ρ (fstA t) ra)
  , subst (R B Δ) (snd-natA t (wkVar ρ)) (monR B ρ (sndA t) rb)
monR (A ⇒ᴬ B) ρ t f = λ Θ σ u ru →
  subst (λ s → R B Θ (appA s u)) (wk-⨟ ρ σ t) (f Θ (ρ ⨟ σ) u ru)

-- REFLECT and REIFY
reflect : (A : TyA) {Γ : CtxA} (n : NeA Γ A) → R A Γ ⌜ n ⌝ne
reify : (A : TyA) {Γ : CtxA} (t : Term Γ A) → R A Γ t
  → ∥ Σ[ n ∈ NfA Γ A ] ⌜ n ⌝nf ≡ t ∥₁

reflect ι n = ∣ neNf n , refl ∣₁
reflect ⊤ᴬ n = tt*
reflect (A ×ᴬ B) n = reflect A (fstNe n) , reflect B (sndNe n)
reflect (A ⇒ᴬ B) {Γ} n Δ ρ u ru =
  PT.rec (isPropR B Δ (appA (wk ρ ⌜ n ⌝ne) u))
    (λ (m , p) →
      subst (R B Δ) (cong₂ appA (wkNe-⌜⌝ ρ n) p)
        (reflect B (appNe (wkNe ρ n) m)))
    (reify A u ru)

reify ι t r = r
reify ⊤ᴬ t _ = ∣ ttNf , sym (⊤ηA t) ∣₁
reify (A ×ᴬ B) t (ra , rb) =
  PT.rec2 squash₁
    (λ (m , p) (n , q) → ∣ pairNf m n , cong₂ pairA p q ∙ ×ηA t ∣₁)
    (reify A (fstA t) ra) (reify B (sndA t) rb)
reify (A ⇒ᴬ B) {Γ} t f =
  PT.map (λ (n , p) → lamNf n , cong lamA p ∙ lem)
    (reify B (appA (wk (wkᶜ {Γ} {A}) t) (varA (inr tt)))
      (f (Γ ,,ᶜ A) wkᶜ (varA (inr tt)) (reflect A (varNe (inr tt)))))
  where
  lem : lamA (appA (wk (wkᶜ {Γ} {A}) t) (varA (inr tt))) ≡ t
  lem =
    cong (λ g → lamA (appA (t ⟨ g ⟩A) (varA (inr tt))))
      (funExt (λ i → substRefl {B = Term (Γ ,,ᶜ A)} (varA (inl i))))
    ∙ ⇒ηA t

-- THE FUNDAMENTAL THEOREM.  The motive is the displayed hom of the
-- glue below: t sends related environments to related results.
-- the motive is the displayed hom of the glue in Multicategory.NbEGlue
D : {I : Type} {Γ : CtxtA I} {A : TyA} → TmA I Γ A → Type₁
D {I} {Γ} {A} t = (Δ : CtxA) (γ : (i : I) → Term Δ (Γ i))
  → ((i : I) → R (Γ i) Δ (γ i)) → R A Δ (t ⟨ γ ⟩A)

private
  isPropD : {I : Type} {Γ : CtxtA I} {A : TyA} (t : TmA I Γ A)
    → isProp (D t)
  isPropD {A = A} t =
    isPropΠ (λ Δ → isPropΠ (λ γ → isPropΠ (λ _ → isPropR A Δ _)))

  dvarᴿ : {I : Type} {Γ : CtxtA I} (i : I) → D (varA {Γ = Γ} i)
  dvarᴿ {Γ = Γ} i Δ γ γR = subst (R (Γ i) Δ) (sym (⟨⟩varA i γ)) (γR i)

  d⟨⟩ᴿ : {I J : Type} {Γ : CtxtA I} {Δ' : CtxtA J} {A : TyA}
    {t : TmA I Γ A} {f : (i : I) → TmA J Δ' (Γ i)}
    → D t → ((i : I) → D (f i)) → D (t ⟨ f ⟩A)
  d⟨⟩ᴿ {A = A} {t = t} {f = f} dt df Δ δ δR =
    subst (R A Δ) (sym (⟨⟩⟨⟩A t f δ))
      (dt Δ (λ i → f i ⟨ δ ⟩A) (λ i → df i Δ δ δR))

  dttᴿ : {I : Type} {Γ : CtxtA I} → D (ttA {I} {Γ})
  dttᴿ Δ γ γR = tt*

  dpairᴿ : {I : Type} {Γ : CtxtA I} {A B : TyA}
    {a : TmA I Γ A} {b : TmA I Γ B} → D a → D b → D (pairA a b)
  dpairᴿ {A = A} {B = B} {a = a} {b = b} da db Δ γ γR =
    subst (R A Δ)
      (sym (cong fstA (pair-natA a b γ) ∙ ×β₁A (a ⟨ γ ⟩A) (b ⟨ γ ⟩A)))
      (da Δ γ γR)
    , subst (R B Δ)
      (sym (cong sndA (pair-natA a b γ) ∙ ×β₂A (a ⟨ γ ⟩A) (b ⟨ γ ⟩A)))
      (db Δ γ γR)

  dfstᴿ : {I : Type} {Γ : CtxtA I} {A B : TyA}
    {t : TmA I Γ (A ×ᴬ B)} → D t → D (fstA t)
  dfstᴿ {A = A} {t = t} dt Δ γ γR =
    subst (R A Δ) (sym (fst-natA t γ)) (dt Δ γ γR .fst)

  dsndᴿ : {I : Type} {Γ : CtxtA I} {A B : TyA}
    {t : TmA I Γ (A ×ᴬ B)} → D t → D (sndA t)
  dsndᴿ {B = B} {t = t} dt Δ γ γR =
    subst (R B Δ) (sym (snd-natA t γ)) (dt Δ γ γR .snd)

  dappᴿ : {I : Type} {Γ : CtxtA I} {A B : TyA}
    {t : TmA I Γ (A ⇒ᴬ B)} {u : TmA I Γ A} → D t → D u → D (appA t u)
  dappᴿ {B = B} {t = t} {u = u} dt du Δ γ γR =
    subst (R B Δ) (sym (app-natA t u γ))
      (subst (λ s → R B Δ (appA s (u ⟨ γ ⟩A))) (wk-id {Δ} (t ⟨ γ ⟩A))
        (dt Δ γ γR Δ (idRen {Δ}) (u ⟨ γ ⟩A) (du Δ γ γR)))

  -- the binder case: weaken the environment, extend it by the
  -- argument, and use that substituting the lifted environment then
  -- the argument is substituting the extended one
  module _ {I : Type} {Γ : CtxtA I} {A B : TyA}
    (t : TmA (I ⊎ Unit) (Γ ,,ᴬ A) B)
    {Δ : CtxA} (γ : (i : I) → Term Δ (Γ i))
    {Θ : CtxA} (ρ : Rename Δ Θ) (u : Term Θ A)
    where
    private
      γ' : (i : I) → Term Θ (Γ i)
      γ' i = wk ρ (γ i)

      γ↑ : (i : I ⊎ Unit) → Term (Θ ,,ᶜ A) ((Γ ,,ᴬ A) i)
      γ↑ = Sum.elim (λ i → γ' i ⟨ (λ j → varA (inl j)) ⟩A)
                      (λ _ → varA (inr tt))

      ext : (i : I ⊎ Unit) → Term Θ ((Γ ,,ᴬ A) i)
      ext = Sum.elim γ' (λ _ → u)

      γ↑-ext : (i : I ⊎ Unit)
        → (γ↑ i ⟨ Sum.elim varA (λ _ → u) ⟩A) ≡ ext i
      γ↑-ext (inl i) =
        ⟨⟩⟨⟩A (γ' i) (λ j → varA (inl j)) (Sum.elim varA (λ _ → u))
        ∙ cong (γ' i ⟨_⟩A)
            (funExt (λ j → ⟨⟩varA (inl j) (Sum.elim varA (λ _ → u))))
        ∙ ⟨⟩idA (γ' i)
      γ↑-ext (inr _) = ⟨⟩varA (inr tt) (Sum.elim varA (λ _ → u))

    lamStep : appA (wk ρ (lamA t ⟨ γ ⟩A)) u ≡ (t ⟨ ext ⟩A)
    lamStep =
      cong (λ s → appA s u)
        (⟨⟩⟨⟩A (lamA t) γ (wkVar ρ)
         ∙ lam-natA t γ' γ↑ (λ i → refl) refl)
      ∙ ⇒βA (t ⟨ γ↑ ⟩A) u (Sum.elim varA (λ _ → u)) (λ i → refl) refl
      ∙ ⟨⟩⟨⟩A t γ↑ (Sum.elim varA (λ _ → u))
      ∙ cong (t ⟨_⟩A) (funExt γ↑-ext)

    extR : ((i : I) → R (Γ i) Δ (γ i)) → R A Θ u
      → (i : I ⊎ Unit) → R ((Γ ,,ᴬ A) i) Θ (ext i)
    extR γR ru = Sum.elim (λ i → monR (Γ i) ρ (γ i) (γR i)) (λ _ → ru)

  dlamᴿ : {I : Type} {Γ : CtxtA I} {A B : TyA}
    {t : TmA (I ⊎ Unit) (Γ ,,ᴬ A) B} → D t → D (lamA t)
  dlamᴿ {A = A} {B = B} {t = t} dt Δ γ γR Θ ρ u ru =
    subst (R B Θ) (sym (lamStep t γ ρ u))
      (dt Θ (Sum.elim (λ i → wk ρ (γ i)) (λ _ → u)) (extR t γ ρ u γR ru))

module FTLR = ElimPropA {D = D} isPropD
  dvarᴿ d⟨⟩ᴿ dttᴿ dpairᴿ dfstᴿ dsndᴿ dlamᴿ dappᴿ

-- the fundamental theorem: every term sends related environments to
-- related results.  This is the S-hom of the section in
-- Multicategory.NbEGlue.
fund : {I : Type} {Γ : CtxtA I} {A : TyA} (t : TmA I Γ A) → D t
fund = FTLR.elimProp

-- NORMALIZATION: every term has a normal form
norm : {Γ : CtxA} {A : TyA} (t : Term Γ A)
  → ∥ Σ[ n ∈ NfA Γ A ] ⌜ n ⌝nf ≡ t ∥₁
norm {Γ} {A} t =
  reify A t
    (subst (R A Γ) (⟨⟩idA t)
      (FTLR.elimProp t Γ varA (λ i → reflect (Typing Γ i) (varNe i))))
