{-

  A model of a sketch in presheaves is a presheaf of models.

  Precisely: for a sketch `S`, a category `C` and a functor
  `M : Functor (S .ind) (PRESHEAF C ℓ)`,

    isModel S (PRESHEAF C ℓ) M ≃ (∀ c → isModel S (SET ℓ) (evPsh c ∘F M))

  (`isModel-pointwise` below).  Both sides are propositions, so a
  logical equivalence suffices and no coherence data is involved.  The
  mathematical content is that limits and colimits of presheaves are
  computed pointwise, which is
  `Cubical.Categories.Presheaf.StrictHom.Pointwise` and its colimit
  mirror `...StrictHom.PointwiseColim`.  Everything here is
  bookkeeping, of two kinds:

  * `funcComp` is not definitionally associative, so the designated
    cones of `evPsh c ∘F M` are only propositionally the evaluations
    of the designated cones of `M`.  The comparison paths are
    `LDiag∘`/`MLCone∘` from `Sketch.Base`; the transports across them
    are cheap because `isLimCone` is a proposition.

  * A sketch records a colimit spec as a diagram into `ind ^op`
    together with a cone in `E ^op`, whereas `PointwiseColim` states
    its theorem for a diagram into `E` together with a cocone.  Since
    `Category` and `Functor` are declared `no-eta-equality`, `J ^op
    ^op` is *not* convertible with `J`, so the two packagings are not
    interchangeable on the nose.  `unopF`/`toCocone`/`fromCocone`
    below convert between them: all the underlying fields do agree
    definitionally, so each conversion is a field-by-field copy, and
    `isLimCone` transfers by applying the hypothesis to the converted
    cone.

  One hypothesis is genuinely needed, and only for the direction
  "model in presheaves ⟹ pointwise model": the proof that a limiting
  cone of presheaves is pointwise limiting goes *through* the
  pointwise limit, so `SET ℓ` must actually have limits of the
  sketch's limit shapes and colimits of its colimit shapes.  The other
  direction, `isModel-fromPointwise`, is unconditional.  For the limit
  half the hypothesis is discharged by `completeSET` whenever the
  levels line up; see the magma corollary at the end of the file.

  NOT proved here: the functorial form
  `MODEL S (PRESHEAF C ℓ) ≃ Functor (C ^op) (MODEL S (SET ℓ))`.  See
  the note at the end of the file.

-}
module Cubical.Algebra.Sketch.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.Pointwise
open import Cubical.Categories.Presheaf.StrictHom.PointwiseColim

open import Cubical.Algebra.Sketch.Base
open import Cubical.Algebra.Sketch.Instances.Magma

private
  variable
    ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓC ℓC' ℓJ ℓJ' ℓE ℓE' ℓ : Level

open Category
open Functor
open Cone

-- A diagram in `E ^op` indexed by `J` is the same data as a diagram in
-- `E` indexed by `J ^op`, and a cone on the former is a cocone on the
-- latter.  Only the packaging differs -- every field agrees on the
-- nose -- but the packaging matters, because a sketch records its
-- colimit specs in the first form while `PointwiseColim` states its
-- theorem in the second.
module _ {J : Category ℓJ ℓJ'} {E : Category ℓE ℓE'}
         (D : Functor J (E ^op)) where

  unopF : Functor (J ^op) E
  unopF .F-ob = D .F-ob
  unopF .F-hom = D .F-hom
  unopF .F-id = D .F-id
  unopF .F-seq f g = D .F-seq g f

  toCocone : {x : E .ob} → Cone {C = E ^op} D x → Cocone unopF x
  toCocone cc .coneOut = cc .coneOut
  toCocone cc .coneOutCommutes = cc .coneOutCommutes

  fromCocone : {x : E .ob} → Cocone unopF x → Cone {C = E ^op} D x
  fromCocone cc .coneOut = cc .coneOut
  fromCocone cc .coneOutCommutes = cc .coneOutCommutes

  module _ {x : E .ob} where
    module _ {cc : Cone {C = E ^op} D x} where
      isLim→isColim : isLimCone {C = E ^op} D x cc
                    → isColimCocone unopF x (toCocone cc)
      isLim→isColim h y cc' = h y (fromCocone cc')

      isColim→isLim : isColimCocone unopF x (toCocone cc)
                    → isLimCone {C = E ^op} D x cc
      isColim→isLim h y cc' = h y (toCocone cc')

module _ (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         {C : Category ℓC ℓC'} {ℓ : Level}
         (M : Functor (Sketch.ind S) (PRESHEAF C ℓ)) where
  open Sketch S

  private
    E : Category _ _
    E = PRESHEAF C ℓ

  -- The limit half.  The evaluation at `c` of the designated cone `i`
  -- of `M` is the designated cone `i` of `evPsh c ∘F M`, once the
  -- non-associativity of `funcComp` is accounted for.
  LConePathP : (i : LIdx) (c : C .ob)
    → PathP (λ j → Cone (LDiag∘ S (evPsh c) M i j) ((M ⟅ LVtx i ⟆) ⟅ c ⟆))
            (evCone c (MLCone S E M i))
            (MLCone S (SET ℓ) (evPsh c ∘F M) i)
  LConePathP i c = conePathPDiag (λ v → refl)

  LStep : (i : LIdx) (c : C .ob)
    → isLimCone (evPsh c ∘F (M ∘F LDiag i)) _ (evCone c (MLCone S E M i))
    ≡ preservesLCone S (SET ℓ) (evPsh c ∘F M) i
  LStep i c j = isLimCone (LDiag∘ S (evPsh c) M i j) _ (LConePathP i c j)

  preservesLCone-pointwise : (i : LIdx)
    → (∀ c → LimCone (evPsh c ∘F (M ∘F LDiag i)))
    → preservesLCone S E M i
    → ∀ c → preservesLCone S (SET ℓ) (evPsh c ∘F M) i
  preservesLCone-pointwise i L p c =
    transport (LStep i c) (isLimCone-pointwise L (MLCone S E M i) p c)

  preservesLCone-fromPointwise : (i : LIdx)
    → (∀ c → preservesLCone S (SET ℓ) (evPsh c ∘F M) i)
    → preservesLCone S E M i
  preservesLCone-fromPointwise i h =
    isLimCone-fromPointwise (MLCone S E M i)
      (λ c → transport (sym (LStep i c)) (h c))

  -- The colimit half.  `CDop i` is the sketch's own packaging of the
  -- i-th designated cocone diagram (a diagram in `E ^op`), and `CD i`
  -- is the same diagram in the form `PointwiseColim` expects.
  CDop : (i : CIdx) → Functor (CShape i) (E ^op)
  CDop i = (M ^opF) ∘F CDiag i

  CD : (i : CIdx) → Functor ((CShape i) ^op) E
  CD i = unopF (CDop i)

  CDev : (i : CIdx) (c : C .ob) → Functor (CShape i) ((SET ℓ) ^op)
  CDev i c = ((evPsh c ∘F M) ^opF) ∘F CDiag i

  CDev≡ : (i : CIdx) (c : C .ob) → evPsh c ∘F CD i ≡ unopF (CDev i c)
  CDev≡ i c = Functor≡ (λ _ → refl) (λ _ → refl)

  CConePathP : (i : CIdx) (c : C .ob)
    → PathP (λ j → Cocone (CDev≡ i c j) ((M ⟅ CVtx i ⟆) ⟅ c ⟆))
            (evCocone c (toCocone (CDop i) (MCCone S E M i)))
            (toCocone (CDev i c) (MCCone S (SET ℓ) (evPsh c ∘F M) i))
  CConePathP i c = conePathPDiag {p = λ j → (CDev≡ i c j) ^opF} (λ v → refl)

  CStep : (i : CIdx) (c : C .ob)
    → isColimCocone (evPsh c ∘F CD i) ((M ⟅ CVtx i ⟆) ⟅ c ⟆)
        (evCocone c (toCocone (CDop i) (MCCone S E M i)))
    ≡ isColimCocone (unopF (CDev i c)) ((M ⟅ CVtx i ⟆) ⟅ c ⟆)
        (toCocone (CDev i c) (MCCone S (SET ℓ) (evPsh c ∘F M) i))
  CStep i c j = isColimCocone (CDev≡ i c j) _ (CConePathP i c j)

  preservesCCone-pointwise : (i : CIdx)
    → (∀ c → ColimCocone (evPsh c ∘F CD i))
    → preservesCCone S E M i
    → ∀ c → preservesCCone S (SET ℓ) (evPsh c ∘F M) i
  preservesCCone-pointwise i L p c =
    isColim→isLim (CDev i c) {cc = MCCone S (SET ℓ) (evPsh c ∘F M) i}
      (transport (CStep i c)
        (isColimCocone-pointwise L (toCocone (CDop i) (MCCone S E M i))
          (isLim→isColim (CDop i) {x = M ⟅ CVtx i ⟆}
            {cc = MCCone S E M i} p) c))

  preservesCCone-fromPointwise : (i : CIdx)
    → (∀ c → preservesCCone S (SET ℓ) (evPsh c ∘F M) i)
    → preservesCCone S E M i
  preservesCCone-fromPointwise i h =
    isColim→isLim (CDop i) {cc = MCCone S E M i}
      (isColimCocone-fromPointwise (toCocone (CDop i) (MCCone S E M i))
        (λ c → transport (sym (CStep i c))
          (isLim→isColim (CDev i c) {x = (M ⟅ CVtx i ⟆) ⟅ c ⟆}
            {cc = MCCone S (SET ℓ) (evPsh c ∘F M) i} (h c))))

  -- Assembling the two halves.  This direction needs no hypotheses.
  isModel-fromPointwise : (∀ c → isModel S (SET ℓ) (evPsh c ∘F M))
                        → isModel S (PRESHEAF C ℓ) M
  isModel-fromPointwise h =
      (λ i → preservesLCone-fromPointwise i (λ c → h c .fst i))
    , (λ i → preservesCCone-fromPointwise i (λ c → h c .snd i))

  -- The converse direction goes through the pointwise (co)limits, so
  -- it needs `SET ℓ` to *have* limits of the sketch's limit shapes and
  -- colimits of its colimit shapes.
  module _ (limSET : ∀ (i : LIdx) (D : Functor (LShape i) (SET ℓ))
                   → LimCone D)
           (colimSET : ∀ (i : CIdx) (D : Functor ((CShape i) ^op) (SET ℓ))
                     → ColimCocone D) where

    isModel-toPointwise : isModel S (PRESHEAF C ℓ) M
                        → ∀ c → isModel S (SET ℓ) (evPsh c ∘F M)
    isModel-toPointwise (pl , pc) c =
        (λ i → preservesLCone-pointwise i (λ c' → limSET i _) (pl i) c)
      , (λ i → preservesCCone-pointwise i (λ c' → colimSET i _) (pc i) c)

    isModel-pointwise : isModel S (PRESHEAF C ℓ) M
                      ≃ (∀ c → isModel S (SET ℓ) (evPsh c ∘F M))
    isModel-pointwise = propBiimpl→Equiv
      (isPropIsModel S (PRESHEAF C ℓ) M)
      (isPropΠ λ c → isPropIsModel S (SET ℓ) (evPsh c ∘F M))
      isModel-toPointwise isModel-fromPointwise

-- The slogan, packaged.  A model of `S` in presheaves on `C` is the
-- same thing as a functor `ind → PRESHEAF C ℓ` all of whose pointwise
-- evaluations are models of `S` in sets: "a model in presheaves is a
-- presheaf of models".  (No extra functoriality has to be imposed on
-- the family of models: it is already there, as the functoriality of
-- the underlying presheaves.)
module _ (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         {C : Category ℓC ℓC'} {ℓ : Level}
         (limSET : ∀ (i : Sketch.LIdx S)
                     (D : Functor (Sketch.LShape S i) (SET ℓ)) → LimCone D)
         (colimSET : ∀ (i : Sketch.CIdx S)
                       (D : Functor ((Sketch.CShape S i) ^op) (SET ℓ))
                     → ColimCocone D) where
  open Sketch S

  modelInPresheaves≃presheafOfModels :
      Model S (PRESHEAF C ℓ)
    ≃ (Σ[ M ∈ Functor ind (PRESHEAF C ℓ) ]
         (∀ (c : C .ob) → isModel S (SET ℓ) (evPsh c ∘F M)))
  modelInPresheaves≃presheafOfModels =
    Σ-cong-equiv-snd λ M → isModel-pointwise S M limSET colimSET

-- Sanity check: the magma sketch.  Its only designated cone has shape
-- the discrete category on two points and it has no designated
-- cocones, so both hypotheses above are discharged outright, by
-- completeness of `SET ℓ-zero`.  The result reads: a presheaf of
-- magmas is a magma in presheaves.
module _ {C : Category ℓC ℓC'} where
  magmaInPresheaves≃presheafOfMagmas :
      Model MagmaSketch (PRESHEAF C ℓ-zero)
    ≃ (Σ[ M ∈ Functor MagmaInd (PRESHEAF C ℓ-zero) ]
         (∀ (c : C .ob) → isModel MagmaSketch (SET ℓ-zero) (evPsh c ∘F M)))
  magmaInPresheaves≃presheafOfMagmas =
    modelInPresheaves≃presheafOfModels MagmaSketch
      (λ _ D → completeSET Two D) (λ ())

{-

  A note on the functorial form.

  The statement one would like next is

    MODEL S (PRESHEAF C ℓ) ≃ Functor (C ^op) (MODEL S (SET ℓ)),

  i.e. the equivalence above upgraded from types of models to
  categories of models.  It is not proved here, and it is not a
  corollary of `isModel-pointwise`: `isModel-pointwise` only reshuffles
  the *property*, whereas the functorial form additionally needs the
  transpose

    Functor ind (PRESHEAF C ℓ) ≃ Functor (C ^op) (Functor ind (SET ℓ)),

  which is a separate construction.  Two obstacles, neither of them
  addressed above:

  * `PRESHEAF C ℓ` has `PshHomStrict` for its morphisms, while the
    currying machinery (`curryF` in `Categories.Instances.Functors.More`)
    is stated for `FUNCTOR (C ^op) (SET ℓ)`, whose morphisms are
    `NatTrans`.  These categories are isomorphic, not equal
    (`PshHom≅PshHomStrict`), so the transpose has to be transported
    along that isomorphism.

  * `curryF` curries out of a product category, so it would first have
    to be composed with the uncurrying
    `Functor ind (FUNCTOR (C ^op) (SET ℓ)) ≃ Functor (ind ×C C ^op) (SET ℓ)`
    and the symmetry of `_×C_`, and then the full subcategory `MODEL`
    would have to be shown to correspond on both sides -- which is
    where `isModel-pointwise` finally enters.

  That is a project of its own, so it is left undone rather than
  half-done.

-}
