{-

  Maps of sketches, and the category they form.

  This mirrors `Cubical.Algebra.Theory.Theories`, which does the same
  for algebraic theories:

    SigMap σ τ      onOps : σ.ops → τ.ops, together with a BACKWARDS
                    map on arities, `unArity`
    SIG             signatures and signature maps
    PresEqns        a PROP: σ's equations survive restriction along a
                    signature map
    reindexModel    a τ-model restricts to a σ-model
    MODReindexᴰ     ... functorially, as a map of displayed model
                    categories
    THEORYᴰ/THEORY  theories displayed over signatures

  VARIANCE.  In `SigMap` the operations go forwards and the arities go
  backwards.  That is exactly what makes restriction of models
  covariant: a τ-algebra `B` interprets the σ-operation `op` by

      ⟦ op ⟧ x = B ⟦ onOps op ⟧ (λ a → x (unArity op a))

  -- the argument tuple `x` is indexed by σ's arity, and it must be
  re-indexed by τ's arity before being handed to `B`, so the map on
  arities must run τ → σ.

  For sketches the same analysis gives:

    * the index category runs FORWARDS, `onInd : S.ind → T.ind`.  A
      model of `T` in `E` is (the model structure on) a functor
      `T.ind → E`, and it is restricted by PRE-composition, so the
      functor must go `S.ind → T.ind` for a `T`-model to restrict to
      an `S`-structure.  This is the analogue of `onOps` for the
      "sorts and structure maps" half of the data.

    * the designated specs run FORWARDS, `onLIdx : S.LIdx → T.LIdx`:
      a designated cone of `S` is named by a designated cone of `T`,
      exactly as an operation of σ is named by an operation of τ.

    * the SHAPES of the designated specs run BACKWARDS,
      `unLShape i : T.LShape (onLIdx i) → S.LShape i`.  The shape
      category of a spec is its arity: the diagram of the S-spec `i`
      is indexed by `S.LShape i`, and to compare it with the T-spec
      `onLIdx i` -- whose diagram is indexed by `T.LShape (onLIdx i)`
      -- it must first be re-indexed along a functor
      `T.LShape (onLIdx i) → S.LShape i`.  This is `unArity`, one
      categorical level up.  `reLCone` below is the resulting
      re-indexed cone; it is the analogue of `reOps`.

  Like `SigMap`, `SketchMap` imposes NO equations on this data.  All of
  the content "the map actually respects the intended semantics" is
  deferred to the displayed layer, i.e. to `PresModel`, exactly as
  `SigMap` defers everything to `PresEqns`.

  STRICT FUNCTORS.  The functors in a `SketchMap` are `StrictFunctor`s
  (`Cubical.Categories.Functors.Strict.Base`), whose functoriality
  clauses are forded and whose composition `_S∘_` is definitionally
  unital and associative.  This buys two things: the category laws of
  `SKETCHIND` are `refl`, as they are for `SIG`; and restricting a
  model structure along `onInd` needs no path algebra at all (see
  `reindexModelStr`), because the forded `F-id`/`F-seq` of the
  `StrictFunctor` are precisely the shape the forded
  `isFunctorialAct` of `Cubical.Algebra.Sketch.Displayed` consumes.

  WHICH MODEL CATEGORY.  `MODELReindexᴰ` is built against the
  DISPLAYED encoding of models of `Cubical.Algebra.Sketch.Displayed`
  (`MODELᴰ` over `Carrier = FAM 𝔼 (ind .ob)`), which is the one that
  mirrors `MODᴰ`.  Note one difference from `MODReindexᴰ`: there, both
  displayed categories sit over the same base `SET ℓX`, so the
  reindexing is a `Functorⱽ`.  Here the base is the object assignment
  `ind .ob → E .ob`, which itself changes along `onInd`, so the
  reindexing is a `Functorᴰ` over the base functor `Carrierᴿ`.  A
  `Functorⱽ` is recovered by reindexing along `Carrierᴿ`
  (`MODELReindexⱽ`).

  CONTENTS.

    restrictF        precomposition with a strict functor
    restrictCone     restriction of a cone along a strict functor
    SketchMap        maps of sketches; `idSketchMap`, `_⋆SketchMap_`,
                     and the three laws, all `refl`
    reLCone/reCCone  the designated (co)cones of `S`, re-indexed along
                     the backwards shape functors
    SKETCHIND        sketches and sketch maps, the analogue of `SIG`
    PresModel        the model-preservation proposition, the analogue
                     of `PresEqns`; `isPropPresModel`
    reindexModel     a `T`-model restricts to an `S`-model
    Carrierᴿ         ... on carriers
    reindexModelStr  ... on model structures
    reindexNatFam    ... on morphisms, the analogue of `reindexHomo`
    MODELReindexᴰ    ... as a `Functorᴰ` over `Carrierᴿ`, and
    MODELReindexⱽ    ... as a `Functorⱽ` into `reindex _ Carrierᴿ`
    SKETCHᴰ/SKETCH   the analogue of `THEORYᴰ`/`THEORY`

  THE DISPLAYED PACKAGING.  `THEORYᴰ` puts the equations of a theory in
  the displayed OBJECTS and equation-preservation in the displayed
  HOMS.  A sketch has no separately chosen equations: the "equations"
  of a designated cone -- that it be sent to a limit -- are canonical,
  determined by the cone itself, and live in `isModel` rather than in
  the `Sketch` record.  So the displayed object layer degenerates to a
  point and `SKETCHᴰ` records only the preservation condition:
  `SKETCH = ∫C SKETCHᴰ` is the category of sketches and
  model-preserving sketch maps, which is the exact analogue of
  `THEORY`.

-}
module Cubical.Algebra.Sketch.Sketches where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Instances.TotalCategory

open import Cubical.Algebra.Sketch.Base
open import Cubical.Algebra.Sketch.Displayed

private
  variable
    ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' : Level
    ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ' : Level
    ℓU ℓU' ℓPI ℓPJ ℓPJ' ℓQI ℓQJ ℓQJ' : Level
    ℓV ℓV' ℓRI ℓRJ ℓRJ' ℓWI ℓWJ ℓWJ' : Level
    ℓE ℓE' ℓJ ℓJ' ℓK ℓK' ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor
open Cone
open Sketch
open StrictFunctor
  renaming (F-ob to S-ob ; F-hom to S-hom ; F-id to S-id ; F-seq to S-seq)

----------------------------------------------------------------------
-- restriction along a strict functor
----------------------------------------------------------------------

-- Precomposition with a strict functor.  We use this rather than
-- `funcComp` throughout: it is the operation that appears in
-- `PresModel`, and its unit/associativity comparisons are the
-- `Functor≡ (λ _ → refl) (λ _ → refl)`s below.
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  where
  restrictF : StrictFunctor C D → Functor D E → Functor C E
  restrictF F N .F-ob x = N .F-ob (F .S-ob x)
  restrictF F N .F-hom f = N .F-hom (F .S-hom f)
  restrictF F N .F-id = cong (N .F-hom) (F .S-id _ refl) ∙ N .F-id
  restrictF F N .F-seq f g =
    cong (N .F-hom) (F .S-seq f g _ refl) ∙ N .F-seq _ _

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  restrictF-SId : (N : Functor C D) → restrictF SId N ≡ N
  restrictF-SId N = Functor≡ (λ _ → refl) (λ _ → refl)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
         {E : Category ℓE ℓE'} {A : Category ℓJ ℓJ'} where
  restrictF-S∘ : (G : StrictFunctor C D) (H : StrictFunctor D E)
                 (N : Functor E A)
               → restrictF (H S∘ G) N ≡ restrictF G (restrictF H N)
  restrictF-S∘ G H N = Functor≡ (λ _ → refl) (λ _ → refl)

-- restriction of a cone along a strict functor on the shape category
module _ {J : Category ℓJ ℓJ'} {K : Category ℓK ℓK'} {C : Category ℓC ℓC'}
  where
  restrictCone : (u : StrictFunctor K J) {D : Functor J C} {c : C .ob}
               → Cone D c → Cone (restrictF u D) c
  restrictCone u cc .coneOut v = cc .coneOut (u .S-ob v)
  restrictCone u cc .coneOutCommutes e = cc .coneOutCommutes (u .S-hom e)

----------------------------------------------------------------------
-- maps of sketches
----------------------------------------------------------------------

private
  ℓSk : (ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' : Level) → Level
  ℓSk ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' =
    ℓ-max (ℓ-max (ℓ-max ℓS ℓS') (ℓ-max ℓLI (ℓ-max ℓLJ ℓLJ')))
          (ℓ-max ℓCI (ℓ-max ℓCJ ℓCJ'))

record SketchMap (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
                 (T : Sketch ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ')
  : Type (ℓ-max (ℓSk ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
                (ℓSk ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ')) where
  field
    -- the index categories run forwards: models restrict by
    -- precomposition
    onInd    : StrictFunctor (S .ind) (T .ind)
    -- designated cones forwards, their shapes backwards
    onLIdx   : S .LIdx → T .LIdx
    unLShape : (i : S .LIdx)
             → StrictFunctor (T .LShape (onLIdx i)) (S .LShape i)
    -- and dually for the designated cocones
    onCIdx   : S .CIdx → T .CIdx
    unCShape : (i : S .CIdx)
             → StrictFunctor (T .CShape (onCIdx i)) (S .CShape i)

open SketchMap

module _ {S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'} where
  idSketchMap : SketchMap S S
  idSketchMap .onInd = SId
  idSketchMap .onLIdx i = i
  idSketchMap .unLShape i = SId
  idSketchMap .onCIdx i = i
  idSketchMap .unCShape i = SId

module _ {S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'}
         {T : Sketch ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ'}
         {U : Sketch ℓU ℓU' ℓPI ℓPJ ℓPJ' ℓQI ℓQJ ℓQJ'}
         (F : SketchMap S T) (G : SketchMap T U) where
  -- exactly `unArity op a = F .unArity op (G .unArity (F .onOps op) a)`
  _⋆SketchMap_ : SketchMap S U
  _⋆SketchMap_ .onInd = G .onInd S∘ F .onInd
  _⋆SketchMap_ .onLIdx i = G .onLIdx (F .onLIdx i)
  _⋆SketchMap_ .unLShape i = F .unLShape i S∘ G .unLShape (F .onLIdx i)
  _⋆SketchMap_ .onCIdx i = G .onCIdx (F .onCIdx i)
  _⋆SketchMap_ .unCShape i = F .unCShape i S∘ G .unCShape (F .onCIdx i)

module _ {S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'}
         {T : Sketch ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ'}
         (F : SketchMap S T) where
  ⋆SketchMapIdL : idSketchMap ⋆SketchMap F ≡ F
  ⋆SketchMapIdL = refl

  ⋆SketchMapIdR : F ⋆SketchMap idSketchMap ≡ F
  ⋆SketchMapIdR = refl

  -- the analogue of `reOps`: the designated cone `i` of `S`,
  -- re-indexed along the backwards shape functor so that it has the
  -- shape of the designated cone `onLIdx i` of `T`
  reLCone : (i : S .LIdx)
          → Cone (restrictF (F .unLShape i) (S .LDiag i)) (S .LVtx i)
  reLCone i = restrictCone (F .unLShape i) (S .LCone i)

  reCCone : (i : S .CIdx)
          → Cone (restrictF (F .unCShape i) (S .CDiag i)) (S .CVtx i)
  reCCone i = restrictCone (F .unCShape i) (S .CCone i)

module _ {S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'}
         {T : Sketch ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ'}
         {U : Sketch ℓU ℓU' ℓPI ℓPJ ℓPJ' ℓQI ℓQJ ℓQJ'}
         {V : Sketch ℓV ℓV' ℓRI ℓRJ ℓRJ' ℓWI ℓWJ ℓWJ'}
         (F : SketchMap S T) (G : SketchMap T U) (H : SketchMap U V)
  where
  ⋆SketchMapAssoc :
    ((F ⋆SketchMap G) ⋆SketchMap H) ≡ (F ⋆SketchMap (G ⋆SketchMap H))
  ⋆SketchMapAssoc = refl

----------------------------------------------------------------------
-- the category of sketches and sketch maps
----------------------------------------------------------------------

-- `SIG`'s objects are signatures equipped with the set-truncation
-- witnesses that make `SigMap` a set.  Here the corresponding data is
-- the set-truncation of the objects of the index category, of the two
-- families of designated specs, and of the objects of their shapes.
module _ (C : Category ℓC ℓC') (D : Category ℓD ℓD') where
  StrictFunctorΣ : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
  StrictFunctorΣ =
    Σ[ Fo ∈ (C .ob → D .ob) ]
    Σ[ Fh ∈ ((x y : C .ob) → C [ x , y ] → D [ Fo x , Fo y ]) ]
      (((x : C .ob) (f : C [ x , x ]) → C .id ≡ f → Fh x x f ≡ D .id)
      × ((x y z : C .ob) (f : C [ x , y ]) (g : C [ y , z ])
         (h : C [ x , z ]) → f ⋆⟨ C ⟩ g ≡ h
         → Fh x z h ≡ Fh x y f ⋆⟨ D ⟩ Fh y z g))

  StrictFunctorIsoΣ : Iso (StrictFunctor C D) StrictFunctorΣ
  StrictFunctorIsoΣ .Iso.fun F =
    F .S-ob , (λ _ _ → F .S-hom) , (λ _ → F .S-id) , (λ _ _ _ → F .S-seq)
  StrictFunctorIsoΣ .Iso.inv (Fo , Fh , Fi , Fs) .S-ob = Fo
  StrictFunctorIsoΣ .Iso.inv (Fo , Fh , Fi , Fs) .S-hom {x} {y} = Fh x y
  StrictFunctorIsoΣ .Iso.inv (Fo , Fh , Fi , Fs) .S-id {x} = Fi x
  StrictFunctorIsoΣ .Iso.inv (Fo , Fh , Fi , Fs) .S-seq {x} {y} {z} = Fs x y z
  StrictFunctorIsoΣ .Iso.sec _ = refl
  StrictFunctorIsoΣ .Iso.ret _ = refl

  isSetStrictFunctor : isSet (D .ob) → isSet (StrictFunctor C D)
  isSetStrictFunctor isSetDob =
    isOfHLevelRetractFromIso 2 StrictFunctorIsoΣ
      (isSetΣ (isSet→ isSetDob) (λ Fo →
        isSetΣ (isSetΠ (λ x → isSetΠ (λ y → isSet→ (D .isSetHom))))
          (λ Fh → isProp→isSet
            (isProp×
              (isPropΠ3 (λ _ _ _ → D .isSetHom _ _))
              (isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ4
                (λ _ _ _ _ → D .isSetHom _ _)))))))))

record SetSketch (ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' : Level)
  : Type (ℓ-suc (ℓSk ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')) where
  field
    skt           : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'
    isSetIndOb    : isSet (skt .ind .ob)
    isSetLIdx     : isSet (skt .LIdx)
    isSetLShapeOb : (i : skt .LIdx) → isSet (skt .LShape i .ob)
    isSetCIdx     : isSet (skt .CIdx)
    isSetCShapeOb : (i : skt .CIdx) → isSet (skt .CShape i .ob)

open SetSketch

module _ (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         (T : Sketch ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ') where
  SketchMapΣ : Type (ℓ-max (ℓSk ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
                           (ℓSk ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ'))
  SketchMapΣ =
    Σ[ Fi ∈ StrictFunctor (S .ind) (T .ind) ]
    Σ[ Fl ∈ (S .LIdx → T .LIdx) ]
    Σ[ _ ∈ ((i : S .LIdx) → StrictFunctor (T .LShape (Fl i)) (S .LShape i)) ]
    Σ[ Fc ∈ (S .CIdx → T .CIdx) ]
      ((i : S .CIdx) → StrictFunctor (T .CShape (Fc i)) (S .CShape i))

  SketchMapIsoΣ : Iso (SketchMap S T) SketchMapΣ
  SketchMapIsoΣ .Iso.fun F =
    F .onInd , F .onLIdx , F .unLShape , F .onCIdx , F .unCShape
  SketchMapIsoΣ .Iso.inv (Fi , Fl , Fu , Fc , Fv) .onInd = Fi
  SketchMapIsoΣ .Iso.inv (Fi , Fl , Fu , Fc , Fv) .onLIdx = Fl
  SketchMapIsoΣ .Iso.inv (Fi , Fl , Fu , Fc , Fv) .unLShape = Fu
  SketchMapIsoΣ .Iso.inv (Fi , Fl , Fu , Fc , Fv) .onCIdx = Fc
  SketchMapIsoΣ .Iso.inv (Fi , Fl , Fu , Fc , Fv) .unCShape = Fv
  SketchMapIsoΣ .Iso.sec _ = refl
  SketchMapIsoΣ .Iso.ret _ = refl

  isSetSketchMap : isSet (T .ind .ob) → isSet (T .LIdx)
                 → ((i : S .LIdx) → isSet (S .LShape i .ob))
                 → isSet (T .CIdx)
                 → ((i : S .CIdx) → isSet (S .CShape i .ob))
                 → isSet (SketchMap S T)
  isSetSketchMap isSetTind isSetTL isSetSLSh isSetTC isSetSCSh =
    isOfHLevelRetractFromIso 2 SketchMapIsoΣ
      (isSetΣ (isSetStrictFunctor _ _ isSetTind) (λ Fi →
        isSetΣ (isSet→ isSetTL) (λ Fl →
          isSetΣ (isSetΠ (λ i → isSetStrictFunctor _ _ (isSetSLSh i)))
            (λ Fu → isSetΣ (isSet→ isSetTC)
              (λ Fc → isSetΠ
                (λ i → isSetStrictFunctor _ _ (isSetSCSh i)))))))

-- sketches and sketch maps.  This is the analogue of `SIG`: it records
-- only the specification data, with all three laws `refl`.
SKETCHIND : ∀ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'
          → Category (ℓ-suc (ℓSk ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'))
                     (ℓSk ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
SKETCHIND ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' .ob =
  SetSketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'
SKETCHIND ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' .Hom[_,_] S T =
  SketchMap (S .skt) (T .skt)
SKETCHIND ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' .id = idSketchMap
SKETCHIND ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ._⋆_ = _⋆SketchMap_
SKETCHIND ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' .⋆IdL f = refl
SKETCHIND ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' .⋆IdR f = refl
SKETCHIND ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' .⋆Assoc f g h = refl
SKETCHIND ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' .isSetHom {x = S} {y = T} =
  isSetSketchMap (S .skt) (T .skt) (T .isSetIndOb) (T .isSetLIdx)
    (S .isSetLShapeOb) (T .isSetCIdx) (S .isSetCShapeOb)

----------------------------------------------------------------------
-- preservation of models
----------------------------------------------------------------------

-- The analogue of `PresEqns`.  `PresEqns σeq τeq ℓX F` says: for every
-- carrier and every τ-algebra on it, the σ-structure obtained by
-- restricting along `F` satisfies σ's equations.  Here: for every
-- ambient category and every T-model in it, the S-structure obtained by
-- restricting along `F .onInd` is an S-model, i.e. it still sends every
-- designated cone of S to a limit and every designated cocone to a
-- colimit.
PresModel : (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
            (T : Sketch ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ')
            (ℓE ℓE' : Level) (F : SketchMap S T) → Type _
PresModel S T ℓE ℓE' F =
  (E : Category ℓE ℓE') (N : Functor (T .ind) E)
  → isModel T E N → isModel S E (restrictF (F .onInd) N)

isPropPresModel : {S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'}
                  {T : Sketch ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ'}
                  {F : SketchMap S T}
                → isProp (PresModel S T ℓE ℓE' F)
isPropPresModel {S = S} = isPropΠ3 (λ E N _ → isPropIsModel S E _)

module _ {S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'} where
  idPresModel : PresModel S S ℓE ℓE' idSketchMap
  idPresModel E N m = subst (isModel S E) (sym (restrictF-SId N)) m

module _ {S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'}
         {T : Sketch ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ'}
         {U : Sketch ℓU ℓU' ℓPI ℓPJ ℓPJ' ℓQI ℓQJ ℓQJ'}
         {F : SketchMap S T} {G : SketchMap T U} where
  seqPresModel : PresModel S T ℓE ℓE' F → PresModel T U ℓE ℓE' G
               → PresModel S U ℓE ℓE' (F ⋆SketchMap G)
  seqPresModel pF pG E N m =
    subst (isModel S E) (sym (restrictF-S∘ (F .onInd) (G .onInd) N))
      (pF E (restrictF (G .onInd) N) (pG E N m))

----------------------------------------------------------------------
-- restriction of models
----------------------------------------------------------------------

module _ {S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ'}
         {T : Sketch ℓT ℓT' ℓMI ℓMJ ℓMJ' ℓNI ℓNJ ℓNJ'}
         (F : SketchMap S T) (E : Category ℓE ℓE') where

  ----------------------------------------------------------------
  -- ... in the sense of `Cubical.Algebra.Sketch.Base`
  ----------------------------------------------------------------

  reindexModel : PresModel S T ℓE ℓE' F → Model T E → Model S E
  reindexModel pF (N , m) = restrictF (F .onInd) N , pF E N m

  ----------------------------------------------------------------
  -- ... and in the displayed sense of `Cubical.Algebra.Sketch.Displayed`
  ----------------------------------------------------------------

  -- The base functor: the object assignment itself is restricted along
  -- `onInd`.  This is what `MODReindexᴰ` does not have to do, its two
  -- displayed categories both sitting over `SET ℓX`.
  Carrierᴿ : Functor (Carrier T E) (Carrier S E)
  Carrierᴿ .F-ob X x = X (F .onInd .S-ob x)
  Carrierᴿ .F-hom α x = α (F .onInd .S-ob x)
  Carrierᴿ .F-id = refl
  Carrierᴿ .F-seq α β = refl

  -- Restriction of a model structure.  No path algebra: the forded
  -- functoriality clauses of the `StrictFunctor` `onInd` are exactly
  -- what the forded `isFunctorialAct` consumes.
  reindexModelStr : {X : T .ind .ob → E .ob}
                  → ModelStr T E X → ModelStr S E (Carrierᴿ .F-ob X)
  reindexModelStr B .fst f = B .fst (F .onInd .S-hom f)
  reindexModelStr B .snd .fst f e =
    B .snd .fst (F .onInd .S-hom f) (sym (F .onInd .S-id f e))
  reindexModelStr B .snd .snd f g h e =
    B .snd .snd (F .onInd .S-hom f) (F .onInd .S-hom g) (F .onInd .S-hom h)
      (sym (F .onInd .S-seq f g h e))

  -- the restricted structure has the restricted underlying functor
  restrictF-toFunctorE : {X : T .ind .ob → E .ob} (B : ModelStr T E X)
    → restrictF (F .onInd) (toFunctorE T E B)
      ≡ toFunctorE S E (reindexModelStr B)
  restrictF-toFunctorE B = Functor≡ (λ _ → refl) (λ _ → refl)

  -- Restriction of a family that is natural for the actions.  This is
  -- the analogue of `reindexHomo`.
  reindexNatFam : {X Y : T .ind .ob → E .ob} {α : Carrier T E [ X , Y ]}
                  {B : ModelStr T E X} {C : ModelStr T E Y}
                → isNatFam T E α B C
                → isNatFam S E (Carrierᴿ .F-hom α)
                    (reindexModelStr B) (reindexModelStr C)
  reindexNatFam ϕ f c h p e = ϕ (F .onInd .S-hom f) c h p e

  module _ (pF : PresModel S T ℓE ℓE' F) where
    reindexModelOb : {X : T .ind .ob → E .ob}
                   → ModelOb T E X → ModelOb S E (Carrierᴿ .F-ob X)
    reindexModelOb (B , m) =
      reindexModelStr B ,
      subst (isModel S E) (restrictF-toFunctorE B)
        (pF E (toFunctorE T E B) m)

    MODELReindexᴰ : Functorᴰ Carrierᴿ (MODELᴰ T E) (MODELᴰ S E)
    MODELReindexᴰ .Functorᴰ.F-obᴰ = reindexModelOb
    MODELReindexᴰ .Functorᴰ.F-homᴰ {x = X} {y = Y} {f = α}
      {xᴰ = B} {yᴰ = C} =
      reindexNatFam {X = X} {Y = Y} {α = α} {B = B .fst} {C = C .fst}
    MODELReindexᴰ .Functorᴰ.F-idᴰ = refl
    MODELReindexᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ = refl

    -- The same functor over `Carrierᴿ ∘F Id`, which is what the
    -- universal property of `reindex` consumes.
    MODELReindexᴰId : Functorᴰ (Carrierᴿ ∘F Id) (MODELᴰ T E) (MODELᴰ S E)
    MODELReindexᴰId .Functorᴰ.F-obᴰ = reindexModelOb
    MODELReindexᴰId .Functorᴰ.F-homᴰ {x = X} {y = Y} {f = α}
      {xᴰ = B} {yᴰ = C} =
      reindexNatFam {X = X} {Y = Y} {α = α} {B = B .fst} {C = C .fst}
    MODELReindexᴰId .Functorᴰ.F-idᴰ {x = X} {xᴰ = B} =
      isProp→PathP
        (λ i → isPropIsNatFam S E
                 {X = Carrierᴿ .F-ob X} {Y = Carrierᴿ .F-ob X}
                 ((Carrierᴿ ∘F Id) .F-id {X} i)
                 (reindexModelStr {X = X} (B .fst))
                 (reindexModelStr {X = X} (B .fst)))
        _ _
    MODELReindexᴰId .Functorᴰ.F-seqᴰ {f = α} {g = β} {xᴰ = B} {zᴰ = D}
      fᴰ gᴰ =
      isProp→PathP
        (λ i → isPropIsNatFam S E ((Carrierᴿ ∘F Id) .F-seq α β i)
                 (reindexModelStr (B .fst)) (reindexModelStr (D .fst)))
        _ _

    -- ... and hence, honestly vertically, into the reindexing of the
    -- S-models along `Carrierᴿ`.  `MODReindexᴰ` is the special case in
    -- which the base functor is the identity, so that no reindexing of
    -- the base is needed.
    MODELReindexⱽ : Functorⱽ (MODELᴰ T E) (reindex (MODELᴰ S E) Carrierᴿ)
    MODELReindexⱽ = introF Id MODELReindexᴰId

----------------------------------------------------------------------
-- the category of sketches and model-preserving sketch maps
----------------------------------------------------------------------

-- The analogue of `THEORYᴰ`.  See the header: a sketch has no chosen
-- equations -- the limit conditions are canonically determined by the
-- designated cones and live in `isModel` -- so the displayed objects
-- are trivial and only the preservation condition is recorded.
SKETCHᴰ : ∀ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE'
        → Categoryᴰ (SKETCHIND ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ') ℓ-zero _
SKETCHᴰ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' .Categoryᴰ.ob[_] S =
  Unit* {ℓ-zero}
SKETCHᴰ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' .Categoryᴰ.Hom[_][_,_]
  {x = S} {y = T} F _ _ = PresModel (S .skt) (T .skt) ℓE ℓE' F
SKETCHᴰ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' .Categoryᴰ.idᴰ {x = S} =
  idPresModel {S = S .skt}
SKETCHᴰ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' .Categoryᴰ._⋆ᴰ_
  {x = S} {y = T} {z = U} {f = F} {g = G} =
  seqPresModel {S = S .skt} {T = T .skt} {U = U .skt} {F = F} {G = G}
SKETCHᴰ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' .Categoryᴰ.⋆IdLᴰ
  {x = S} {y = T} {f = F} fᴰ =
  isPropPresModel {S = S .skt} {T = T .skt} {F = F} _ _
SKETCHᴰ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' .Categoryᴰ.⋆IdRᴰ
  {x = S} {y = T} {f = F} fᴰ =
  isPropPresModel {S = S .skt} {T = T .skt} {F = F} _ _
SKETCHᴰ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' .Categoryᴰ.⋆Assocᴰ
  {x = S} {w = V} {f = F} {g = G} {h = H} fᴰ gᴰ hᴰ =
  isPropPresModel {S = S .skt} {T = V .skt}
    {F = F ⋆SketchMap (G ⋆SketchMap H)} _ _
SKETCHᴰ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' .Categoryᴰ.isSetHomᴰ
  {x = S} {y = T} {f = F} =
  isProp→isSet (isPropPresModel {S = S .skt} {T = T .skt} {F = F})

SKETCH : ∀ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' → Category _ _
SKETCH ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE' =
  ∫C (SKETCHᴰ ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' ℓE ℓE')
