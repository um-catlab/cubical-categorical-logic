{-

  FREE MODELS OF A SKETCH.

  This is the sketch analogue of `Cubical.Algebra.Theory.Free.Explicit`
  + `Cubical.Algebra.Theory.Free.Section`: a HIT `Free`, a proof that
  it is a model, a recursor, and the universal property exhibiting it
  as the free model on a family of generators.

  ------------------------------------------------------------------
  1.  THE GENERAL CASE: FREE MODELS OF A SKETCH DO NOT EXIST.
  ------------------------------------------------------------------

  For an algebraic theory the free model exists for soft reasons: the
  forgetful functor `MOD → SET` is monadic.  For a *sketch* this fails,
  and not because of any limitation of Agda -- it is false.

  A sketch has both designated cones (to become limits) and designated
  cocones (to become colimits).  Lair's theorem says that the
  categories of models of small mixed sketches are, up to equivalence,
  exactly the *accessible* categories.  Accessible categories need not
  be cocomplete, need not be reflective in the ambient functor
  category, and in particular need not have an initial object.

  The standard counterexample is the category of fields.  It is the
  category of models of a mixed sketch (a limit sketch presents
  commutative rings; a single designated *co*cone expressing the
  carrier as the coproduct `{0} + (units)` cuts the models down to
  fields).  It is accessible, and it has NO initial object: a field has
  characteristic `0` or `p`, field homomorphisms preserve
  characteristic and there are no homomorphisms between fields of
  different characteristic, so no field admits a map to every field.

  Since `FreeOb (λ _ → ⊥*)` would be exactly an initial object of
  `MODEL S E` -- that is how `Cubical.Algebra.Theory.Free.Section`
  derives `InitialMOD` from `UPMod` -- the free model of a general
  sketch cannot exist.  This is a *theorem*, not a formalisation
  obstacle: there is nothing to build, and any "free model of an
  arbitrary sketch" would be wrong.

  So the honest question is: for which sketches does it exist, and can
  those be built here?

  ------------------------------------------------------------------
  2.  LIMIT SKETCHES: EXISTS CLASSICALLY, BY A TRANSFINITE ARGUMENT.
  ------------------------------------------------------------------

  Drop the cocones.  Models of a limit sketch in `SET` form a locally
  presentable category and the inclusion

      MODEL S (SET ℓ)  ↪  FUNCTOR ind (SET ℓ)

  is reflective.  Under the Yoneda lemma the condition "`M` sends the
  `i`-th designated cone to a limit" is orthogonality of `M` against
  the canonical map

      κ i : colim_j ind [ LDiag i j ,-]  →  ind [ LVtx i ,-]

  so the models are the orthogonality class `κ ⊥`, and the reflection
  is produced by the *small object argument*: repeatedly (a) glue in a
  mediating element for every compatible family that lacks one, and
  (b) quotient by the uniqueness of mediating elements, then iterate
  transfinitely and take the colimit of the chain.

  Both halves of that are hostile here.  (b) is a quotient by a
  relation generated at each stage, which without `SetQuotient` we
  cannot form directly; and the transfinite iteration needs an
  ordinal-indexed chain together with a proof that it converges, which
  is a substantial amount of infrastructure that does not exist in
  this library.

  ------------------------------------------------------------------
  3.  WHAT THIS FILE DOES INSTEAD.
  ------------------------------------------------------------------

  A HIT performs the transfinite iteration *and* the quotienting in
  one step, for free.  `Free` below has

    gen          the generators,
    act          formal action of the index morphisms,
    actId/actSeq the functoriality equations,
    med          a formal mediating element for every compatible
                 family of elements over a designated cone,
    medβ         its projections are the family it was built from,
    medη         uniqueness: anything with those projections IS that
                 mediator (`medηPath` is the "every element of the
                 vertex is the mediator of its own projections" form),
    trunc        set truncation.

  The inductive type is the colimit of the "glue in mediators" chain
  (a mediator is built from strictly smaller data, which is exactly
  the convergence the small object argument has to prove by hand), and
  `medη` is the uniqueness quotient imposed as a path constructor
  rather than as a set-quotient.  `medβ` and `medη` together say
  precisely that the cone at `LVtx i` is a limit cone.

  THE ONE THING THAT MAKES THIS WORK, AND THAT COULD HAVE FAILED.
  The compatibility condition on the family carried by `med` is

      act (LDiag i .F-hom e) (t j) ≡ t j'

  which is a *path in the very type being defined*, appearing as an
  argument of a constructor.  Agda accepts this (`PathP`'s type
  argument is a positive position), and -- crucially -- the resulting
  recursion is still structural: in `rec (med i t c)` every recursive
  call is `rec (t j)` on constructor data, and the coherence is
  transported by `cong rec ∘ c`, which is *not* a recursive call.  So
  no `TERMINATING` pragma and no fusion lemma is needed.

  That last point is delicate and dictated the shape of `medη`.  The
  first attempt stated it in the computed form

      med i (λ j → act (LCone i .coneOut j) u) <coherence> ≡ u

  where `<coherence>` had to be spelled out inline as
  `sym (actSeq ..) ∙ cong (λ h → act h u) (coneOutCommutes e)`.  Then
  `rec`'s clause for that constructor must apply `rec` to
  `(sym (actSeq ..) ∙ ..) i`, which is not a subterm of the pattern,
  and the termination checker rejects it -- the same failure mode as
  `Theory.Free`, reached from a different direction.  Taking the
  compatible family and the coherence as *arguments* of `medη`, i.e.
  stating uniqueness rather than the computed η, makes every coherence
  that `rec` sees a pattern variable, and the recursion goes through.

  Contrast `Cubical.Algebra.Theory.Free`, whose recursor does not
  exist because its `eqn` constructor mentions `TmRec node ρ`, an
  external recursive function applied to the whole term, forcing a
  fusion lemma whose `node` case calls `rec` at a non-subterm.  Nothing
  of that shape occurs here: `medβ`/`medη` mention only constructors
  applied to subterms.  This is why the sketch presentation needs no
  explicit-substitution trick, and why (unlike
  `Theory.Free.Explicit`) there is no level bump from quantifying over
  a `{W : Type ℓv}` inside a constructor.

  SCOPE.  Everything below is for a sketch `S` together with a proof
  `noC : CIdx → ⊥` that it has no designated cocones, and for models
  in `SET`.  Within that scope the shapes `LShape i` are *arbitrary*
  small categories: this is not restricted to discrete cones
  (products), it covers equalizers, pullbacks, and any other limit
  specification.  What is genuinely out of reach is:

    * mixed sketches -- impossible, see 1;
    * models in an ambient category other than `SET` (or a presheaf
      category), because `med` needs *elements*: the free model is
      built from generalized elements at the terminal object and there
      is no reason for a general `E` to have a generating object.

  NOT DONE, and known to be missing.

    * The universal property is proved against `MODEL S (SET ℓ)` from
      `Sketch.Base`, where a morphism of models is literally a natural
      transformation.  The displayed `MODEL∫` of `Sketch.Displayed`
      gets the free model as an *object* (`FreeModel∫` below), but not
      the hom-level universal property; that needs
      `isFullyFaithful ∫→MODEL`, which nobody has proved.

    * No formal bridge to `Cubical.Algebra.Theory.Free.Explicit`.
      Saying "the algebraic-theory `FreeModel` is the sketch free
      model of the corresponding sketch" first requires building the
      Lawvere-style index category of a signature, whose objects are
      the arities and whose designated cones are all the arity-indexed
      products; that construction does not exist in this library.  The
      instance `Cubical.Algebra.Sketch.Free.Magma` does the comparison
      by hand for one sketch: the free model of `MagmaSketch` has
      `FM ⟨X²⟩ ≅ FM ⟨X⟩ × FM ⟨X⟩` and a binary operation on `FM ⟨X⟩`.

-}
module Cubical.Algebra.Sketch.Free.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥ ; ⊥*)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Instances.Sets

open import Cubical.Algebra.Sketch.Base
open import Cubical.Algebra.Sketch.Displayed

private
  variable
    ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓN ℓv : Level

open Category
open Functor
open NatTrans
open Cone

----------------------------------------------------------------------
-- The mediating-element interface of a model in `SET`.
--
-- `isModel` is phrased with `isLimCone`, which quantifies over cones
-- from an arbitrary object.  Instantiating at the singleton set turns
-- it into the "elementwise" statement we actually use: a compatible
-- family of elements has a unique mediating element.
----------------------------------------------------------------------

module _ (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         (N : Functor (Sketch.ind S) (SET ℓN)) where
  open Sketch S

  -- a family of elements, one over each vertex of the `i`-th diagram,
  -- compatible with the action of the shape morphisms
  isCompatFam : (i : LIdx)
    → ((j : LShape i .ob) → ⟨ N .F-ob (LDiag i .F-ob j) ⟩) → Type _
  isCompatFam i t =
    {j j' : LShape i .ob} (e : LShape i [ j , j' ])
    → N .F-hom (LDiag i .F-hom e) (t j) ≡ t j'

  isPropIsCompatFam : (i : LIdx)
    (t : (j : LShape i .ob) → ⟨ N .F-ob (LDiag i .F-ob j) ⟩)
    → isProp (isCompatFam i t)
  isPropIsCompatFam i t =
    isPropImplicitΠ2 (λ _ _ → isPropΠ (λ _ → N .F-ob _ .snd _ _))

  private
    UnitS : hSet ℓN
    UnitS = Unit* , isSetUnit*

  module _ (i : LIdx)
    (t : (j : LShape i .ob) → ⟨ N .F-ob (LDiag i .F-ob j) ⟩)
    (c : isCompatFam i t) where

    elemCone : Cone (funcComp N (LDiag i)) UnitS
    elemCone .coneOut j _ = t j
    elemCone .coneOutCommutes e = funExt (λ _ → c e)

    module _ (lim : preservesLCone S (SET ℓN) N i) where
      private
        ctr = lim UnitS elemCone

      mediate : ⟨ N .F-ob (LVtx i) ⟩
      mediate = ctr .fst .fst tt*

      mediateβ : (j : LShape i .ob)
        → N .F-hom (LCone i .coneOut j) mediate ≡ t j
      mediateβ j = funExt⁻ (ctr .fst .snd j) tt*

      mediateUniq : (x : ⟨ N .F-ob (LVtx i) ⟩)
        → ((j : LShape i .ob) → N .F-hom (LCone i .coneOut j) x ≡ t j)
        → x ≡ mediate
      mediateUniq x p =
        sym (funExt⁻
          (cong fst (ctr .snd ((λ _ → x) , (λ j → funExt (λ _ → p j)))))
          tt*)

----------------------------------------------------------------------
-- The free model on a family of generators.
----------------------------------------------------------------------

ℓFree : (ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓv : Level) → Level
ℓFree ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓv =
  ℓ-max ℓS (ℓ-max ℓS' (ℓ-max ℓLI (ℓ-max ℓLJ (ℓ-max ℓLJ' ℓv))))

module _ (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         (V : Sketch.ind S .ob → Type ℓv) where
  open Sketch S

  private
    ℓF = ℓFree ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓv

  data Free : ind .ob → Type ℓF where
    gen : {a : ind .ob} → V a → Free a
    act : {a b : ind .ob} → ind [ a , b ] → Free a → Free b
    actId : {a : ind .ob} (x : Free a) → act (ind .id) x ≡ x
    actSeq : {a b c : ind .ob}
      (f : ind [ a , b ]) (g : ind [ b , c ]) (x : Free a)
      → act (f ⋆⟨ ind ⟩ g) x ≡ act g (act f x)
    med : (i : LIdx) (t : (j : LShape i .ob) → Free (LDiag i .F-ob j))
      → ({j j' : LShape i .ob} (e : LShape i [ j , j' ])
         → act (LDiag i .F-hom e) (t j) ≡ t j')
      → Free (LVtx i)
    medβ : (i : LIdx) (t : (j : LShape i .ob) → Free (LDiag i .F-ob j))
      (ct : {j j' : LShape i .ob} (e : LShape i [ j , j' ])
            → act (LDiag i .F-hom e) (t j) ≡ t j')
      (j : LShape i .ob)
      → act (LCone i .coneOut j) (med i t ct) ≡ t j
    -- uniqueness of mediating elements.  Stated with the compatible
    -- family as an *argument* rather than as the computed family
    -- `λ j → act (LCone i .coneOut j) u`: that keeps every coherence
    -- appearing in `rec` a pattern variable, which is what makes the
    -- recursion structural.  The computed form is `medηPath` below.
    medη : (i : LIdx) (t : (j : LShape i .ob) → Free (LDiag i .F-ob j))
      (ct : {j j' : LShape i .ob} (e : LShape i [ j , j' ])
            → act (LDiag i .F-hom e) (t j) ≡ t j')
      (u : Free (LVtx i))
      → ((j : LShape i .ob) → act (LCone i .coneOut j) u ≡ t j)
      → u ≡ med i t ct
    trunc : {a : ind .ob} → isSet (Free a)

  -- the compatibility condition, named after the fact
  Compat : (i : LIdx) → ((j : LShape i .ob) → Free (LDiag i .F-ob j))
    → Type (ℓ-max ℓLJ (ℓ-max ℓLJ' ℓF))
  Compat i t = {j j' : LShape i .ob} (e : LShape i [ j , j' ])
    → act (LDiag i .F-hom e) (t j) ≡ t j'

  isPropCompat : (i : LIdx)
    (t : (j : LShape i .ob) → Free (LDiag i .F-ob j))
    → isProp (Compat i t)
  isPropCompat i t =
    isPropImplicitΠ2 (λ _ _ → isPropΠ (λ _ → trunc _ _))

  -- the projections of an element of the vertex are compatible
  projCompat : (i : LIdx) (u : Free (LVtx i))
    → Compat i (λ j → act (LCone i .coneOut j) u)
  projCompat i u {j} e =
    sym (actSeq (LCone i .coneOut j) (LDiag i .F-hom e) u)
    ∙ cong (λ h → act h u) (LCone i .coneOutCommutes e)

  -- the computed form of `medη`: every element of the vertex is the
  -- mediator of its own projections
  medηPath : (i : LIdx) (u : Free (LVtx i))
    → med i (λ j → act (LCone i .coneOut j) u) (projCompat i u) ≡ u
  medηPath i u =
    sym (medη i (λ j → act (LCone i .coneOut j) u) (projCompat i u) u
          (λ _ → refl))

  -- `med` does not depend on the compatibility proof
  medPath : (i : LIdx)
    {t t' : (j : LShape i .ob) → Free (LDiag i .F-ob j)}
    (p : (j : LShape i .ob) → t j ≡ t' j)
    (ct : Compat i t) (ct' : Compat i t')
    → med i t ct ≡ med i t' ct'
  medPath i {t} {t'} p ct ct' k =
    med i (λ j → p j k)
      (isProp→PathP (λ k → isPropCompat i (λ j → p j k)) ct ct' k)

  -- The elementwise content of "the designated cones became limits":
  -- an element of the vertex is exactly a compatible family.
  medIso : (i : LIdx)
    → Iso (Free (LVtx i))
          (Σ[ t ∈ ((j : LShape i .ob) → Free (LDiag i .F-ob j)) ]
             Compat i t)
  medIso i .Iso.fun u = (λ j → act (LCone i .coneOut j) u) , projCompat i u
  medIso i .Iso.inv (t , ct) = med i t ct
  medIso i .Iso.sec (t , ct) =
    Σ≡Prop (isPropCompat i) (funExt (λ j → medβ i t ct j))
  medIso i .Iso.ret = medηPath i

  FreeSet : (a : ind .ob) → hSet ℓF
  FreeSet a = Free a , trunc

  FreeFunctor : Functor ind (SET ℓF)
  FreeFunctor .F-ob = FreeSet
  FreeFunctor .F-hom = act
  FreeFunctor .F-id = funExt actId
  FreeFunctor .F-seq f g = funExt (actSeq f g)

  -- `medβ` and `medη` are exactly the limit property
  isLimFree : (i : LIdx) → preservesLCone S (SET ℓF) FreeFunctor i
  isLimFree i c cc =
    uniqueExists h hmor
      (isPropIsConeMor cc (MLCone S (SET ℓF) FreeFunctor i)) uniq
    where
    hfam : ⟨ c ⟩ → (j : LShape i .ob) → Free (LDiag i .F-ob j)
    hfam x j = cc .coneOut j x

    hcoh : (x : ⟨ c ⟩) → Compat i (hfam x)
    hcoh x e = funExt⁻ (cc .coneOutCommutes e) x

    h : ⟨ c ⟩ → Free (LVtx i)
    h x = med i (hfam x) (hcoh x)

    hmor : isConeMor cc (MLCone S (SET ℓF) FreeFunctor i) h
    hmor j = funExt (λ x → medβ i (hfam x) (hcoh x) j)

    uniq : (g : SET ℓF [ c , FreeSet (LVtx i) ])
      → isConeMor cc (MLCone S (SET ℓF) FreeFunctor i) g → h ≡ g
    uniq g gmor = funExt (λ x →
      sym (medη i (hfam x) (hcoh x) (g x) (λ j → funExt⁻ (gmor j) x)))

  ------------------------------------------------------------------
  -- the propositional eliminator
  ------------------------------------------------------------------

  module _ {ℓP : Level} (P : {a : ind .ob} → Free a → Type ℓP)
    (isPropP : {a : ind .ob} (x : Free a) → isProp (P x))
    (pgen : {a : ind .ob} (v : V a) → P (gen v))
    (pact : {a b : ind .ob} (f : ind [ a , b ]) {x : Free a}
      → P x → P (act f x))
    (pmed : (i : LIdx)
      (t : (j : LShape i .ob) → Free (LDiag i .F-ob j)) (ct : Compat i t)
      → ((j : LShape i .ob) → P (t j)) → P (med i t ct))
    where

    elimProp : {a : ind .ob} (x : Free a) → P x
    elimProp (gen v) = pgen v
    elimProp (act f x) = pact f (elimProp x)
    elimProp (actId x k) =
      isProp→PathP (λ k → isPropP (actId x k))
        (pact (ind .id) (elimProp x)) (elimProp x) k
    elimProp (actSeq f g x k) =
      isProp→PathP (λ k → isPropP (actSeq f g x k))
        (pact (f ⋆⟨ ind ⟩ g) (elimProp x))
        (pact g (pact f (elimProp x))) k
    elimProp (med i t ct) = pmed i t ct (λ j → elimProp (t j))
    elimProp (medβ i t ct j k) =
      isProp→PathP (λ k → isPropP (medβ i t ct j k))
        (pact (LCone i .coneOut j) (pmed i t ct (λ j' → elimProp (t j'))))
        (elimProp (t j)) k
    elimProp (medη i t ct u p k) =
      isProp→PathP (λ k → isPropP (medη i t ct u p k))
        (elimProp u) (pmed i t ct (λ j → elimProp (t j))) k
    elimProp (trunc x y p q k l) =
      isProp→SquareP (λ k l → isPropP (trunc x y p q k l))
        (λ _ → elimProp x) (λ _ → elimProp y)
        (λ m → elimProp (p m)) (λ m → elimProp (q m)) k l

  ------------------------------------------------------------------
  -- the recursor
  ------------------------------------------------------------------

  module _ (N : Functor ind (SET ℓN))
           (limN : (i : LIdx) → preservesLCone S (SET ℓN) N i) where

    module _ (ρ : (a : ind .ob) → V a → ⟨ N .F-ob a ⟩) where

      rec : {a : ind .ob} → Free a → ⟨ N .F-ob a ⟩
      rec (gen v) = ρ _ v
      rec (act f x) = N .F-hom f (rec x)
      rec (actId x k) = funExt⁻ (N .F-id) (rec x) k
      rec (actSeq f g x k) = funExt⁻ (N .F-seq f g) (rec x) k
      rec (med i t ct) =
        mediate S N i (λ j → rec (t j))
          (λ e → cong (λ z → rec z) (ct e)) (limN i)
      rec (medβ i t ct j k) =
        mediateβ S N i (λ j' → rec (t j'))
          (λ e → cong (λ z → rec z) (ct e)) (limN i) j k
      rec (medη i t ct u p k) =
        mediateUniq S N i (λ j → rec (t j))
          (λ e → cong (λ z → rec z) (ct e)) (limN i) (rec u)
          (λ j → cong (λ z → rec z) (p j)) k
      rec (trunc x y p q k l) =
        N .F-ob _ .snd (rec x) (rec y)
          (cong (λ z → rec z) p) (cong (λ z → rec z) q) k l

      recβ : {a : ind .ob} (v : V a) → rec (gen v) ≡ ρ a v
      recβ v = refl

      -- naturality is definitional: `rec (act f x) = N .F-hom f (rec x)`
      recNatHom : {a b : ind .ob} (f : ind [ a , b ]) (x : Free a)
        → rec (act f x) ≡ N .F-hom f (rec x)
      recNatHom f x = refl

    -- `rec ρ` is the unique natural family sending `gen v` to `ρ v`
    module _ (ρ : (a : ind .ob) → V a → ⟨ N .F-ob a ⟩)
             (f : (a : ind .ob) → Free a → ⟨ N .F-ob a ⟩)
             (fnat : {a b : ind .ob} (g : ind [ a , b ]) (x : Free a)
                   → f b (act g x) ≡ N .F-hom g (f a x))
             (fβ : (a : ind .ob) (v : V a) → f a (gen v) ≡ ρ a v)
      where

      private
        P : {a : ind .ob} → Free a → Type ℓN
        P {a} x = f a x ≡ rec ρ x

        isPropP : {a : ind .ob} (x : Free a) → isProp (P x)
        isPropP {a} x = N .F-ob a .snd _ _

        pact : {a b : ind .ob} (g : ind [ a , b ]) {x : Free a}
          → P x → P (act g x)
        pact g {x} ih = fnat g x ∙ cong (N .F-hom g) ih

        pmed : (i : LIdx)
          (t : (j : LShape i .ob) → Free (LDiag i .F-ob j))
          (ct : Compat i t)
          → ((j : LShape i .ob) → P (t j)) → P (med i t ct)
        pmed i t ct ih =
          mediateUniq S N i (λ j → rec ρ (t j))
            (λ e → cong (λ z → rec ρ z) (ct e)) (limN i)
            (f (LVtx i) (med i t ct))
            (λ j → sym (fnat (LCone i .coneOut j) (med i t ct))
                   ∙ cong (f (LDiag i .F-ob j)) (medβ i t ct j)
                   ∙ ih j)

      recUniq : (a : ind .ob) (x : Free a) → f a x ≡ rec ρ x
      recUniq a x = elimProp P isPropP (λ {b} v → fβ b v) pact pmed x

  ------------------------------------------------------------------
  -- the universal property
  ------------------------------------------------------------------

  module _ (noC : CIdx → ⊥) where

    FreeModel : Model S (SET ℓF)
    FreeModel .fst = FreeFunctor
    FreeModel .snd .fst = isLimFree
    FreeModel .snd .snd i = Empty.rec (noC i)

    -- `FreeModel` is free on `V`: a morphism of models out of it is
    -- exactly a family of elements chosen for the generators.  A
    -- morphism of models is a natural transformation, because `MODEL`
    -- is a full subcategory of the functor category.
    UPModel : (N : MODEL S (SET ℓF) .ob)
      → Iso (MODEL S (SET ℓF) [ FreeModel , N ])
            ((a : ind .ob) → V a → ⟨ N .fst .F-ob a ⟩)
    UPModel N .Iso.fun α a v = α .N-ob a (gen v)
    UPModel N .Iso.inv ρ .N-ob a = rec (N .fst) (N .snd .fst) ρ
    UPModel N .Iso.inv ρ .N-hom g = refl
    UPModel N .Iso.sec ρ = refl
    UPModel N .Iso.ret α =
      makeNatTransPath (funExt (λ a → funExt (λ x →
        sym (recUniq (N .fst) (N .snd .fst)
              (λ b v → α .N-ob b (gen v)) (α .N-ob)
              (λ g x' → funExt⁻ (α .N-hom g) x') (λ _ _ → refl) a x))))

----------------------------------------------------------------------
-- The free model as an object of the displayed model category.
--
-- `Cubical.Algebra.Sketch.Displayed` proves `ModelObIso`, which says
-- that its `MODEL∫` and `Base.agda`'s `Model` have the same objects,
-- and gives the comparison functor `∫→MODEL`.  Transporting the free
-- model across it is all that is needed to place it there; the
-- universal property itself is proved above against `MODEL`, which is
-- where a morphism of models is literally a natural transformation.
----------------------------------------------------------------------

module _ (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         (V : Sketch.ind S .ob → Type ℓv)
         (noC : Sketch.CIdx S → ⊥) where

  private
    ℓF = ℓFree ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓv

  FreeModel∫ : MODEL∫ S (SET ℓF) .ob
  FreeModel∫ = ModelObIso S (SET ℓF) .Iso.inv (FreeModel S V noC)

  ∫→MODEL-FreeModel∫ :
    ∫→MODEL S (SET ℓF) .F-ob FreeModel∫ ≡ FreeModel S V noC
  ∫→MODEL-FreeModel∫ = ModelObIso S (SET ℓF) .Iso.sec (FreeModel S V noC)

----------------------------------------------------------------------
-- Initiality: the free model on no generators is initial.
----------------------------------------------------------------------

module _ (ℓg : Level) (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         (noC : Sketch.CIdx S → ⊥) where
  open Sketch S

  private
    ℓF = ℓFree ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓg

    V₀ : ind .ob → Type ℓg
    V₀ _ = ⊥*

  InitialModel : Model S (SET ℓF)
  InitialModel = FreeModel S V₀ noC

  isInitialFreeModel : isInitial (MODEL S (SET ℓF)) (FreeModel S V₀ noC)
  isInitialFreeModel N =
    isOfHLevelRetractFromIso 0 (UPModel S V₀ noC N)
      ((λ _ ()) , (λ _ → funExt (λ _ → funExt (λ ()))))

  InitialMODEL : Initial (MODEL S (SET ℓF))
  InitialMODEL = FreeModel S V₀ noC , isInitialFreeModel
