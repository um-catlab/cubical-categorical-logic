{-

  EACH TYPE FORMER OF Multicategory.Syntax IS A UNIVERSAL PROPERTY.

  The syntax is CARTESIAN CLOSED: its formers are ⊤', _×'_ and _⇒'_,
  and nothing else.  The three constructions below say that every one
  of them is determined by a bijection of hom-sets, and that the
  bijection is witnessed by its own elimination (resp. introduction)
  rule.  Read `Tm I Γ A` as the hom-set `Syn(Γ ; A)` of the free
  cartesian multicategory; then

    ⊤UP   Tm I Γ ⊤'          ≅ Unit
    ×UP   Tm I Γ (A ×' B)    ≅ Tm I Γ A × Tm I Γ B
    ⇒UP   Tm I Γ (A ⇒' B)    ≅ Tm (I ⊎ Unit) (Γ ,, A) B

  All three are natural in Γ, so ⊤', A ×' B and A ⇒' B REPRESENT the
  presheaves `Unit`, `Tm(-,A) × Tm(-,B)` and `Tm(- ,, A , B)` on the
  multicategory of contexts, and the universal element of each is its
  ELIMINATOR:

    ⊤'       the unique element                 (no eliminator)
    A ×' B   the pair (fst' , snd') of the generic term of A ×' B
    A ⇒' B   app of the weakened generic term to the fresh variable

  In every case the β laws are the round trip in one direction and the
  η law is the round trip in the other.  (`sec` and `ret` are this
  cubical's names for the two round trips of an Iso; elsewhere they are
  called rightInv and leftInv.)

    ⊤   ret = ⊤η                     (no β: Unit is contractible)
    ×   sec = ×β₁ , ×β₂ ;            ret = ×η
    ⇒   sec = lam-nat ∙ ⇒β ∙ clone ; ret = ⇒η

  The clone laws (⟪⟫var / ⟪⟫id / ⟪⟫⟪⟫) and the naturality path
  constructors are what let the FORDED substitutions in ⇒β and lam-nat
  be instantiated: since those rules take the substitution as a
  parameter together with equations pinning it, one may simply DEFINE
  the substitution to be the wanted `Sum.elim` and discharge the ford
  witnesses by `refl`.  That is the whole technique used below; no
  equation of the theory is needed beyond the ones named above.


  DOES Multicategory.Elim's DisplayedModel FACTOR AS THREE DISPLAYED
  UNIVERSAL ELEMENTS?  Honest assessment, from the shapes met here.

  YES — and that is precisely what dropping sums bought.  Every former
  of a cartesian closed syntax is FIBREWISE: each of the three round
  trips below stays inside one fibre of the displayed multicategory,
  so each package is a displayed universal element in that fibre.

  * ⊤'.  Two fields, `ttᴰ` and `⊤ηᴰ`.  These are exactly (displayed
    element, displayed uniqueness) — a displayed universal element of
    the terminal displayed presheaf, i.e. `isContr` displayed.  There
    is no `tt-natᴰ` field and none is needed, because ⊤η already forces
    tt' ⟪ f ⟫ ≡ tt'.  This one factors on the nose.

  * A ×' B.  SIX fields — pairᴰ / fstᴰ / sndᴰ / ×β₁ᴰ / ×β₂ᴰ / ×ηᴰ —
    plus THREE naturality fields pair-natᴰ / fst-natᴰ / snd-natᴰ.  The
    six are the displayed vertex + displayed universal element +
    displayed β + displayed η of a displayed representation, exactly as
    ×UP's four Iso fields are.  The three -nat fields are the second
    half of "REPRESENTATION", not residue: an Iso is not a
    representation until it is an Iso of PRESHEAVES.  See
    `fst-generic` and `genericSubst-nat` at the bottom of this file:
    fst-nat is equivalent to saying that fst' is substitution into the
    single generic element `fst' (var tt)` of the one-variable context
    [ A ×' B ], and once an operation has that form its naturality is
    the clone law ⟪⟫⟪⟫ and nothing else.  So the -nat fields are
    ABSORBED by a genuine universal-element presentation (where the
    operation is defined by substituting into the universal element)
    but must be carried explicitly by this presentation (where the
    operation is a constructor at every context).  Factors, once the
    universal element is put in the one-variable context.

  * A ⇒' B.  lamᴰ / appᴰ / ⇒βᴰ / ⇒ηᴰ (four) + app-natᴰ, lam-natᴰ.  The
    four match ⇒UP's four Iso fields one-for-one, INCLUDING the shape
    of the forded arguments: ⇒βᴰ takes `fᴰ : (i : I ⊎ Unit) → ⟦ f i ⟧ᴰ`
    over the forded substitution, which is precisely the displayed
    image of the substitution I have to supply by hand in ⇒rightInv.
    ⇒η is not forded — its environment is literally `λ j → var (inl j)`
    — so ⇒ηᴰ needs no substitution parameter at all.  The
    correspondence is tight enough that it is fair to say ⇒'s six
    fields = one displayed universal element (four fields) + two
    naturality residues.

  SUMMARY.  DisplayedModel has 18 fields: S-ob, 6 point fields, 11 law
  fields.  They split as

    S-ob                                                       1
    ⊤'  package   ttᴰ ⊤ηᴰ                                       2
    ×'  package   pairᴰ fstᴰ sndᴰ ×β₁ᴰ ×β₂ᴰ ×ηᴰ                  6
    ⇒'  package   lamᴰ appᴰ ⇒βᴰ ⇒ηᴰ                              4
    naturality    pair-nat fst-nat snd-nat app-nat lam-nat      5

  (the 3 clone laws ⋆Varᴰ / ⋆Idᴰ / ⋆Assocᴰ are already supplied by the
  ambient CartesianMulticategoryᴰ, and there is no tt-nat because ⊤η
  subsumes it).  So YES for the 12 = 2+6+4, with one caveat: the 5
  naturality fields are the "Iso of presheaves" half of each package
  rather than a fourth thing — they are absorbed exactly when the
  operation is presented as substitution into a generic element, cf.
  fst-generic below.

-}
module Multicategory.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum hiding (elim; rec)
open import Cubical.Data.Unit

open import Multicategory.Syntax

open Iso

-- ---------------------------------------------------------------
-- ⊤' : Tm I Γ ⊤' ≅ Unit.  Purely ⊤η.
-- ---------------------------------------------------------------

⊤UP : (I : Type) (Γ : Ctxt I) → Iso (Tm I Γ ⊤') Unit
⊤UP I Γ .fun _ = tt
⊤UP I Γ .inv _ = tt' {I} {Γ}
⊤UP I Γ .sec _ = refl
⊤UP I Γ .ret t = sym (⊤η t)

-- ---------------------------------------------------------------
-- A ×' B : Tm I Γ (A ×' B) ≅ Tm I Γ A × Tm I Γ B.
-- The universal element is (fst' , snd'); β is the section, η the
-- retraction.
-- ---------------------------------------------------------------

×UP : (I : Type) (Γ : Ctxt I) (A B : Ty)
  → Iso (Tm I Γ (A ×' B)) (Tm I Γ A × Tm I Γ B)
×UP I Γ A B .fun t = fst' t , snd' t
×UP I Γ A B .inv ab = pair (ab .fst) (ab .snd)
×UP I Γ A B .sec ab =
  ΣPathP (×β₁ (ab .fst) (ab .snd) , ×β₂ (ab .fst) (ab .snd))
×UP I Γ A B .ret t = ×η t

-- ---------------------------------------------------------------
-- A ⇒' B : Tm I Γ (A ⇒' B) ≅ Tm (I ⊎ Unit) (Γ ,, A) B.
--
-- The universal element is `app (v ⟪ wk ⟫) v0`, the eliminator applied
-- to the generic term of A ⇒' B and the fresh variable.  `inv` is lam.
-- ---------------------------------------------------------------

module ⇒Universal (I : Type) (Γ : Ctxt I) (A B : Ty) where

  -- the weakening (Γ) → (Γ ,, A)
  wk : (i : I) → Tm (I ⊎ Unit) (Γ ,, A) (Γ i)
  wk i = var (inl i)

  -- the universal element: eliminate the generic term
  ε : Tm I Γ (A ⇒' B) → Tm (I ⊎ Unit) (Γ ,, A) B
  ε t = app (t ⟪ (λ j → var (inl j)) ⟫) (var (inr tt))

  private
    -- lam-nat's forded lift of `wk` to (Γ ,, A) ,, A
    f↑ : (i : I ⊎ Unit) → Tm ((I ⊎ Unit) ⊎ Unit) ((Γ ,, A) ,, A) ((Γ ,, A) i)
    f↑ = Sum.elim (λ i → var (inl (inl i))) (λ _ → var (inr tt))

    -- ⇒β's forded "extend by u", here u = the fresh variable
    g : (i : (I ⊎ Unit) ⊎ Unit)
      → Tm (I ⊎ Unit) (Γ ,, A) (((Γ ,, A) ,, A) i)
    g = Sum.elim var (λ _ → var (inr tt))

    -- the composite of the two forded substitutions is the identity
    collapse : (i : I ⊎ Unit) → (f↑ i ⟪ g ⟫) ≡ var {I ⊎ Unit} {Γ ,, A} i
    collapse = Sum.elim (λ i → ⟪⟫var (inl (inl i)) g) (λ _ → ⟪⟫var (inr tt) g)

    ⇒rightInv : (u : Tm (I ⊎ Unit) (Γ ,, A) B) → ε (lam u) ≡ u
    ⇒rightInv u =
      cong (λ s → app s (var (inr tt)))
        (lam-nat u (λ j → var (inl j)) f↑
          (λ i → sym (⟪⟫var (inl i) (λ j → var (inl j)))) refl)
      ∙ ⇒β (u ⟪ f↑ ⟫) (var (inr tt)) g (λ i → refl) refl
      ∙ ⟪⟫⟪⟫ u f↑ g
      ∙ cong (u ⟪_⟫) (funExt collapse)
      ∙ ⟪⟫id u

  ⇒UP : Iso (Tm I Γ (A ⇒' B)) (Tm (I ⊎ Unit) (Γ ,, A) B)
  ⇒UP .fun = ε
  ⇒UP .inv = lam
  ⇒UP .sec = ⇒rightInv
  ⇒UP .ret t = ⇒η t

open ⇒Universal using (⇒UP) public

-- ---------------------------------------------------------------
-- WHAT THE NATURALITY PATH CONSTRUCTORS ARE.
--
-- An Iso is not yet a representation: a representation is an Iso of
-- PRESHEAVES, i.e. one whose components commute with substitution.
-- The naturality constructors (fst-nat, snd-nat, app-nat, inl-nat, …)
-- are exactly that, and the following two lemmas say precisely what
-- they buy.
--
-- `genericSubst-nat`: anything of the form "substitute into a fixed
-- element" is natural for free — the proof is the clone law ⟪⟫⟪⟫ and
-- nothing else.
--
-- `fst-generic`: fst' IS of that form, namely substitution into the
-- eliminator applied to the single generic variable of type A ×' B.
-- The proof needs fst-nat, so the implication runs both ways: the
-- naturality constructor is EQUIVALENT to saying that the eliminator
-- is substitution into one generic element.  It is therefore not an
-- extra law on top of the universal property but the statement that
-- the universal element exists in the one-variable context and
-- generates the rest — which is what "universal element" means.
-- ---------------------------------------------------------------

-- the one-variable context on X
[_] : Ty → Ctxt Unit
[ X ] _ = X

genericSubst-nat : {K : Type} {Θ : Ctxt K} {X : Ty} (e : Tm K Θ X)
  {I J : Type} {Γ : Ctxt I} {Δ : Ctxt J}
  (σ : (k : K) → Tm I Γ (Θ k)) (f : (i : I) → Tm J Δ (Γ i))
  → ((e ⟪ σ ⟫) ⟪ f ⟫) ≡ (e ⟪ (λ k → σ k ⟪ f ⟫) ⟫)
genericSubst-nat e σ f = ⟪⟫⟪⟫ e σ f

fst-generic : {I : Type} {Γ : Ctxt I} {A B : Ty} (t : Tm I Γ (A ×' B))
  → fst' t ≡ (fst' (var {Unit} {[ A ×' B ]} tt) ⟪ (λ _ → t) ⟫)
fst-generic t =
  sym (fst-nat (var tt) (λ _ → t) ∙ cong fst' (⟪⟫var tt (λ _ → t)))

snd-generic : {I : Type} {Γ : Ctxt I} {A B : Ty} (t : Tm I Γ (A ×' B))
  → snd' t ≡ (snd' (var {Unit} {[ A ×' B ]} tt) ⟪ (λ _ → t) ⟫)
snd-generic t =
  sym (snd-nat (var tt) (λ _ → t) ∙ cong snd' (⟪⟫var tt (λ _ → t)))
