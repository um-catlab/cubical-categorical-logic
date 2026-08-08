{-

  EACH TYPE FORMER OF Multicategory.Syntax IS A UNIVERSAL PROPERTY.

  The four constructions below say that every former of the syntax is
  determined by a bijection of hom-sets, and that the bijection is
  witnessed by its own elimination (resp. introduction) rule.  Read
  `Tm I Γ A` as the hom-set `Syn(Γ ; A)` of the free cartesian
  multicategory; then

    ⊤UP   Tm I Γ ⊤'          ≅ Unit
    ×UP   Tm I Γ (A ×' B)    ≅ Tm I Γ A × Tm I Γ B
    ⇒UP   Tm I Γ (A ⇒' B)    ≅ Tm (I ⊎ Unit) (Γ ,, A) B
    +UP   Tm (I ⊎ Unit) (Γ ,, (A +' B)) C
                             ≅ Tm (I ⊎ Unit) (Γ ,, A) C
                             × Tm (I ⊎ Unit) (Γ ,, B) C

  The first three are natural in Γ, so ⊤', A ×' B and A ⇒' B
  REPRESENT the presheaves `Unit`, `Tm(-,A) × Tm(-,B)` and
  `Tm(- ,, A , B)` on the multicategory of contexts, and the universal
  element of each is its ELIMINATOR:

    ⊤'       the unique element                 (no eliminator)
    A ×' B   the pair (fst' , snd') of the generic term of A ×' B
    A ⇒' B   app of the weakened generic term to the fresh variable

  The last is natural in the OTHER variable, so A +' B COREPRESENTS,
  and its universal element is its INTRODUCER: the pair
  (inl' v0 , inr' v0) of coprojections, which is exactly the pair of
  substitutions `gA` / `gB` below.

  In every case the β laws are the round trip in one direction and the
  η law is the round trip in the other.  (`sec` and `ret` are this
  cubical's names for the two round trips of an Iso; elsewhere they are
  called rightInv and leftInv.)

    ⊤   ret = ⊤η                     (no β: Unit is contractible)
    ×   sec = ×β₁ , ×β₂ ;            ret = ×η
    ⇒   sec = lam-nat ∙ ⇒β ∙ clone ; ret = ⇒η
    +   sec = case-nat ∙ +β₁/+β₂ ∙ clone ;  ret = +η

  The clone laws (⟪⟫var / ⟪⟫id / ⟪⟫⟪⟫) and the naturality path
  constructors are what let the FORDED substitutions in ⇒β, +β₁, +β₂,
  lam-nat, case-nat and +η be instantiated: since those rules take the
  substitution as a parameter together with equations pinning it, one
  may simply DEFINE the substitution to be the wanted `Sum.elim` and
  discharge the ford witnesses by `refl`.  That is the whole technique
  used below; no equation of the theory is needed beyond the ones
  named above.


  DOES Multicategory.Elim's DisplayedModel FACTOR AS FOUR DISPLAYED
  UNIVERSAL ELEMENTS?  Honest assessment, from the shapes met here.

  MOSTLY YES.  Every field is accounted for by one of the four
  packages, but the four are not all the same KIND of universal
  element: three are fibrewise and the sum's is not.

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
    image of the substitution I have to supply by hand in ⇒rightInv,
    and ⇒ηᴰ takes the extra `wᴰ` over the weakening — the displayed
    image of the `λ j → var (inl j)` that ⇒UP.fun uses.  The
    correspondence is tight enough that it is fair to say ⇒'s six
    fields = one displayed universal element (four fields) + two
    naturality residues.

  * A +' B.  inlᴰ / inrᴰ / caseᴰ / +β₁ᴰ / +β₂ᴰ / +ηᴰ + inl-natᴰ /
    inr-natᴰ / case-natᴰ.  This is where the factorization visibly
    FAILS to be as clean as the other three, for a reason that is
    already visible in +UP: the corepresentation is a statement about
    the hom-set out of an EXTENDED context, `Tm (I ⊎ Unit) (Γ ,, (A +'
    B)) C`, and its two round trips do not stay inside one fibre of the
    displayed multicategory.  Concretely, +UP.sec needs case-nat,
    +β₁ and TWO clone-law collapses just to state the round trip, and
    +UP.ret needs +η at a scrutinee (`var (inr tt)`) and a
    displayed term `h ⟪ m ⟫` living over a context that is neither the
    source nor the target of the bijection.  Correspondingly +ηᴰ has
    THREE displayed substitution arguments (fᴰ, gᴬᴰ, gᴮᴰ) over three
    different extended contexts, where ⇒ηᴰ has one.  Those three cannot
    be recovered from a single displayed universal element in a single
    fibre; they are the displayed form of the three substitutions that
    +UP has to name explicitly.  So +' factors only if one first has a
    notion of displayed universal element that is allowed to quantify
    over the substitutions into extended contexts — i.e. a displayed
    universal element of a presheaf on the SLICE, not on the fibre.

  SUMMARY.  DisplayedModel has 27 fields: S-ob, 9 point fields, 17 law
  fields.  They split as

    S-ob                                                       1
    ⊤'  package   ttᴰ ⊤ηᴰ                                       2
    ×'  package   pairᴰ fstᴰ sndᴰ ×β₁ᴰ ×β₂ᴰ ×ηᴰ                  6
    ⇒'  package   lamᴰ appᴰ ⇒βᴰ ⇒ηᴰ                              4
    +'  package   inlᴰ inrᴰ caseᴰ +β₁ᴰ +β₂ᴰ +ηᴰ                  6
    naturality    pair-nat fst-nat snd-nat app-nat lam-nat
                  inl-nat inr-nat case-nat                      8

  (the 3 clone laws ⋆Varᴰ / ⋆Idᴰ / ⋆Assocᴰ are already supplied by the
  ambient CartesianMulticategoryᴰ, and there is no tt-nat because ⊤η
  subsumes it).  So YES for the 18 = 2+6+4+6, with two caveats: the 8
  naturality fields are the "Iso of presheaves" half of each package
  rather than a fourth thing (they are absorbed exactly when the
  operation is presented as substitution into a generic element, cf.
  fst-generic below), and the ⊤'/×'/⇒' packages are displayed
  universal elements in a FIBRE whereas the +' package is not — its η
  quantifies over three substitutions into three different extended
  contexts, so it needs a slice-level, not fibre-level, notion of
  displayed universal element.

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
-- A +' B : Tm (I ⊎ Unit) (Γ ,, (A +' B)) C
--          ≅ Tm (I ⊎ Unit) (Γ ,, A) C × Tm (I ⊎ Unit) (Γ ,, B) C.
--
-- Here A +' B COREPRESENTS: the universal element is the pair of
-- coprojections (inl' v0 , inr' v0), acting by substitution.  `inv` is
-- case' on the fresh variable.
-- ---------------------------------------------------------------

module +Universal (I : Type) (Γ : Ctxt I) (A B C : Ty) where

  -- the two coprojections, as substitutions (Γ ,, (A +' B)) → (Γ ,, A)
  -- and (Γ ,, (A +' B)) → (Γ ,, B).  This pair IS the universal
  -- element of the corepresentation.
  gA : (i : I ⊎ Unit) → Tm (I ⊎ Unit) (Γ ,, A) ((Γ ,, (A +' B)) i)
  gA = Sum.elim (λ i → var (inl i)) (λ _ → inl' {B = B} (var (inr tt)))

  gB : (i : I ⊎ Unit) → Tm (I ⊎ Unit) (Γ ,, B) ((Γ ,, (A +' B)) i)
  gB = Sum.elim (λ i → var (inl i)) (λ _ → inr' {A = A} (var (inr tt)))

  private
    -- weakenings used to move a branch into the scope of the scrutinee
    wA : (i : I ⊎ Unit)
      → Tm ((I ⊎ Unit) ⊎ Unit) ((Γ ,, (A +' B)) ,, A) ((Γ ,, A) i)
    wA = Sum.elim (λ i → var (inl (inl i))) (λ _ → var (inr tt))

    wB : (i : I ⊎ Unit)
      → Tm ((I ⊎ Unit) ⊎ Unit) ((Γ ,, (A +' B)) ,, B) ((Γ ,, B) i)
    wB = Sum.elim (λ i → var (inl (inl i))) (λ _ → var (inr tt))

  ε : Tm (I ⊎ Unit) (Γ ,, (A +' B)) C
    → Tm (I ⊎ Unit) (Γ ,, A) C × Tm (I ⊎ Unit) (Γ ,, B) C
  ε h = (h ⟪ gA ⟫) , (h ⟪ gB ⟫)

  split : Tm (I ⊎ Unit) (Γ ,, A) C → Tm (I ⊎ Unit) (Γ ,, B) C
    → Tm (I ⊎ Unit) (Γ ,, (A +' B)) C
  split l r = case' (var (inr tt)) (l ⟪ wA ⟫) (r ⟪ wB ⟫)

  ----------------------------------------------------------------
  -- rightInv: the β direction.  case-nat pushes gA inside, ⟪⟫var
  -- exposes the scrutinee as inl' v0, +β₁ fires, and two clone-law
  -- collapses reduce the remaining substitution to the identity.
  ----------------------------------------------------------------
  private
    -- case-nat's forded lifts of gA
    fAA : (i : (I ⊎ Unit) ⊎ Unit)
      → Tm ((I ⊎ Unit) ⊎ Unit) ((Γ ,, A) ,, A) (((Γ ,, (A +' B)) ,, A) i)
    fAA = Sum.elim (λ i → gA i ⟪ (λ j → var (inl j)) ⟫) (λ _ → var (inr tt))

    fAB : (i : (I ⊎ Unit) ⊎ Unit)
      → Tm ((I ⊎ Unit) ⊎ Unit) ((Γ ,, A) ,, B) (((Γ ,, (A +' B)) ,, B) i)
    fAB = Sum.elim (λ i → gA i ⟪ (λ j → var (inl j)) ⟫) (λ _ → var (inr tt))

    fBA : (i : (I ⊎ Unit) ⊎ Unit)
      → Tm ((I ⊎ Unit) ⊎ Unit) ((Γ ,, B) ,, A) (((Γ ,, (A +' B)) ,, A) i)
    fBA = Sum.elim (λ i → gB i ⟪ (λ j → var (inl j)) ⟫) (λ _ → var (inr tt))

    fBB : (i : (I ⊎ Unit) ⊎ Unit)
      → Tm ((I ⊎ Unit) ⊎ Unit) ((Γ ,, B) ,, B) (((Γ ,, (A +' B)) ,, B) i)
    fBB = Sum.elim (λ i → gB i ⟪ (λ j → var (inl j)) ⟫) (λ _ → var (inr tt))

    -- +β₁ / +β₂'s forded "extend by the fresh variable"
    sA : (i : (I ⊎ Unit) ⊎ Unit)
      → Tm (I ⊎ Unit) (Γ ,, A) (((Γ ,, A) ,, A) i)
    sA = Sum.elim var (λ _ → var (inr tt))

    sB : (i : (I ⊎ Unit) ⊎ Unit)
      → Tm (I ⊎ Unit) (Γ ,, B) (((Γ ,, B) ,, B) i)
    sB = Sum.elim var (λ _ → var (inr tt))

    collapseA : (i : I ⊎ Unit)
      → ((wA i ⟪ fAA ⟫) ⟪ sA ⟫) ≡ var {I ⊎ Unit} {Γ ,, A} i
    collapseA =
      Sum.elim
        (λ i → cong (_⟪ sA ⟫)
                 (⟪⟫var (inl (inl i)) fAA
                  ∙ ⟪⟫var (inl i) (λ j → var (inl j)))
               ∙ ⟪⟫var (inl (inl i)) sA)
        (λ _ → cong (_⟪ sA ⟫) (⟪⟫var (inr tt) fAA) ∙ ⟪⟫var (inr tt) sA)

    collapseB : (i : I ⊎ Unit)
      → ((wB i ⟪ fBB ⟫) ⟪ sB ⟫) ≡ var {I ⊎ Unit} {Γ ,, B} i
    collapseB =
      Sum.elim
        (λ i → cong (_⟪ sB ⟫)
                 (⟪⟫var (inl (inl i)) fBB
                  ∙ ⟪⟫var (inl i) (λ j → var (inl j)))
               ∙ ⟪⟫var (inl (inl i)) sB)
        (λ _ → cong (_⟪ sB ⟫) (⟪⟫var (inr tt) fBB) ∙ ⟪⟫var (inr tt) sB)

    rightA : (l : Tm (I ⊎ Unit) (Γ ,, A) C) (r : Tm (I ⊎ Unit) (Γ ,, B) C)
      → (split l r ⟪ gA ⟫) ≡ l
    rightA l r =
      case-nat (var (inr tt)) (l ⟪ wA ⟫) (r ⟪ wB ⟫) gA
        fAA (λ i → refl) refl fAB (λ i → refl) refl
      ∙ cong (λ s → case' s ((l ⟪ wA ⟫) ⟪ fAA ⟫) ((r ⟪ wB ⟫) ⟪ fAB ⟫))
          (⟪⟫var (inr tt) gA)
      ∙ +β₁ (var (inr tt)) ((l ⟪ wA ⟫) ⟪ fAA ⟫) ((r ⟪ wB ⟫) ⟪ fAB ⟫)
          sA (λ i → refl) refl
      ∙ cong (_⟪ sA ⟫) (⟪⟫⟪⟫ l wA fAA)
      ∙ ⟪⟫⟪⟫ l (λ i → wA i ⟪ fAA ⟫) sA
      ∙ cong (l ⟪_⟫) (funExt collapseA)
      ∙ ⟪⟫id l

    rightB : (l : Tm (I ⊎ Unit) (Γ ,, A) C) (r : Tm (I ⊎ Unit) (Γ ,, B) C)
      → (split l r ⟪ gB ⟫) ≡ r
    rightB l r =
      case-nat (var (inr tt)) (l ⟪ wA ⟫) (r ⟪ wB ⟫) gB
        fBA (λ i → refl) refl fBB (λ i → refl) refl
      ∙ cong (λ s → case' s ((l ⟪ wA ⟫) ⟪ fBA ⟫) ((r ⟪ wB ⟫) ⟪ fBB ⟫))
          (⟪⟫var (inr tt) gB)
      ∙ +β₂ (var (inr tt)) ((l ⟪ wA ⟫) ⟪ fBA ⟫) ((r ⟪ wB ⟫) ⟪ fBB ⟫)
          sB (λ i → refl) refl
      ∙ cong (_⟪ sB ⟫) (⟪⟫⟪⟫ r wB fBB)
      ∙ ⟪⟫⟪⟫ r (λ i → wB i ⟪ fBB ⟫) sB
      ∙ cong (r ⟪_⟫) (funExt collapseB)
      ∙ ⟪⟫id r

  ----------------------------------------------------------------
  -- leftInv: the η direction, i.e. +η at the scrutinee `var (inr tt)`.
  -- +η is stated about a term in a context extended by a SECOND copy
  -- of A +' B, so the term we feed it is `h ⟪ m ⟫` for the middle
  -- weakening m; the three forded substitutions of +η are then the
  -- three Sum.elims below.
  ----------------------------------------------------------------
  private
    m : (i : I ⊎ Unit)
      → Tm ((I ⊎ Unit) ⊎ Unit) ((Γ ,, (A +' B)) ,, (A +' B))
          ((Γ ,, (A +' B)) i)
    m = Sum.elim (λ i → var (inl (inl i))) (λ _ → var (inr tt))

    -- +η's `f`: pinned to be the identity on the old variables and the
    -- scrutinee on the new one
    fη : (i : (I ⊎ Unit) ⊎ Unit)
      → Tm (I ⊎ Unit) (Γ ,, (A +' B))
          (((Γ ,, (A +' B)) ,, (A +' B)) i)
    fη = Sum.elim var (λ _ → var (inr tt))

    -- +η's two coprojection substitutions, one level up from gA / gB
    gA' : (i : (I ⊎ Unit) ⊎ Unit)
      → Tm ((I ⊎ Unit) ⊎ Unit) ((Γ ,, (A +' B)) ,, A)
          (((Γ ,, (A +' B)) ,, (A +' B)) i)
    gA' = Sum.elim (λ i → var (inl i)) (λ _ → inl' {B = B} (var (inr tt)))

    gB' : (i : (I ⊎ Unit) ⊎ Unit)
      → Tm ((I ⊎ Unit) ⊎ Unit) ((Γ ,, (A +' B)) ,, B)
          (((Γ ,, (A +' B)) ,, (A +' B)) i)
    gB' = Sum.elim (λ i → var (inl i)) (λ _ → inr' {A = A} (var (inr tt)))

    -- m followed by fη is the identity substitution
    mfη : (i : I ⊎ Unit)
      → (m i ⟪ fη ⟫) ≡ var {I ⊎ Unit} {Γ ,, (A +' B)} i
    mfη = Sum.elim (λ i → ⟪⟫var (inl (inl i)) fη) (λ _ → ⟪⟫var (inr tt) fη)

    -- m followed by gA' is gA followed by wA (and likewise for B):
    -- this is what identifies +η's branches with ε's components.
    mgA : (i : I ⊎ Unit) → (m i ⟪ gA' ⟫) ≡ (gA i ⟪ wA ⟫)
    mgA =
      Sum.elim
        (λ i → ⟪⟫var (inl (inl i)) gA' ∙ sym (⟪⟫var (inl i) wA))
        (λ _ → ⟪⟫var (inr tt) gA'
               ∙ sym (inl-nat (var (inr tt)) wA
                      ∙ cong (inl' {B = B}) (⟪⟫var (inr tt) wA)))

    mgB : (i : I ⊎ Unit) → (m i ⟪ gB' ⟫) ≡ (gB i ⟪ wB ⟫)
    mgB =
      Sum.elim
        (λ i → ⟪⟫var (inl (inl i)) gB' ∙ sym (⟪⟫var (inl i) wB))
        (λ _ → ⟪⟫var (inr tt) gB'
               ∙ sym (inr-nat (var (inr tt)) wB
                      ∙ cong (inr' {A = A}) (⟪⟫var (inr tt) wB)))

    branchA : (h : Tm (I ⊎ Unit) (Γ ,, (A +' B)) C)
      → ((h ⟪ m ⟫) ⟪ gA' ⟫) ≡ ((h ⟪ gA ⟫) ⟪ wA ⟫)
    branchA h =
      ⟪⟫⟪⟫ h m gA'
      ∙ cong (h ⟪_⟫) (funExt mgA)
      ∙ sym (⟪⟫⟪⟫ h gA wA)

    branchB : (h : Tm (I ⊎ Unit) (Γ ,, (A +' B)) C)
      → ((h ⟪ m ⟫) ⟪ gB' ⟫) ≡ ((h ⟪ gB ⟫) ⟪ wB ⟫)
    branchB h =
      ⟪⟫⟪⟫ h m gB'
      ∙ cong (h ⟪_⟫) (funExt mgB)
      ∙ sym (⟪⟫⟪⟫ h gB wB)

    leftη : (h : Tm (I ⊎ Unit) (Γ ,, (A +' B)) C)
      → split (h ⟪ gA ⟫) (h ⟪ gB ⟫) ≡ h
    leftη h =
      cong₂ (case' (var (inr tt))) (sym (branchA h)) (sym (branchB h))
      ∙ sym (+η (var (inr tt)) (h ⟪ m ⟫) fη (λ i → refl) refl
               gA' (λ i → refl) refl gB' (λ i → refl) refl)
      ∙ ⟪⟫⟪⟫ h m fη
      ∙ cong (h ⟪_⟫) (funExt mfη)
      ∙ ⟪⟫id h

  +UP : Iso (Tm (I ⊎ Unit) (Γ ,, (A +' B)) C)
            (Tm (I ⊎ Unit) (Γ ,, A) C × Tm (I ⊎ Unit) (Γ ,, B) C)
  +UP .fun = ε
  +UP .inv lr = split (lr .fst) (lr .snd)
  +UP .sec lr =
    ΣPathP (rightA (lr .fst) (lr .snd) , rightB (lr .fst) (lr .snd))
  +UP .ret = leftη

open +Universal using (+UP) public

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
