{-

  Sketches and their models.

  A *sketch* is an index category `ind` equipped with a family of
  designated cones and a family of designated cocones.  A *model* of a
  sketch in a category `E` is a functor `M : Functor ind E` sending
  each designated cone to a limit cone and each designated cocone to a
  colimit cocone.

  This is the most general notion of "theory" whose models in a
  presheaf category are computed pointwise, since both limits and
  colimits of presheaves are pointwise.

  Following the standing convention of this library, colimits are
  handled *by duality*: a cocone on a diagram in `ind` is literally a
  cone on a diagram in `ind ^op`, so the colimit half of a sketch is
  recorded as diagrams into `ind ^op` and the colimit condition on a
  model is `isLimCone` in `E ^op`.

-}
module Cubical.Algebra.Sketch.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.FullSubcategory

private
  variable
    ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' : Level

open Category
open Functor

record Sketch (ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ' : Level)
  : Type (ℓ-suc (ℓ-max (ℓ-max (ℓ-max ℓS ℓS')
                              (ℓ-max ℓLI (ℓ-max ℓLJ ℓLJ')))
                       (ℓ-max ℓCI (ℓ-max ℓCJ ℓCJ')))) where
  no-eta-equality
  field
    -- the underlying index category
    ind : Category ℓS ℓS'

    -- designated cones, to be sent to limits
    LIdx   : Type ℓLI
    LShape : LIdx → Category ℓLJ ℓLJ'
    LDiag  : (i : LIdx) → Functor (LShape i) ind
    LVtx   : LIdx → ind .ob
    LCone  : (i : LIdx) → Cone (LDiag i) (LVtx i)

    -- designated cocones, to be sent to colimits.  A cocone on a
    -- diagram in `ind` is a cone on a diagram in `ind ^op`.
    CIdx   : Type ℓCI
    CShape : CIdx → Category ℓCJ ℓCJ'
    CDiag  : (i : CIdx) → Functor (CShape i) (ind ^op)
    CVtx   : CIdx → ind .ob
    CCone  : (i : CIdx) → Cone (CDiag i) (CVtx i)

module _ {ℓE ℓE' : Level}
         (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         (E : Category ℓE ℓE') where
  open Sketch S

  -- the image of the i-th designated cone under a functor
  MLCone : (M : Functor ind E) (i : LIdx)
         → Cone (funcComp M (LDiag i)) (M .F-ob (LVtx i))
  MLCone M i = F-cone M (LCone i)

  -- the image of the i-th designated cocone under a functor, read as
  -- a cone in the opposite categories
  MCCone : (M : Functor ind E) (i : CIdx)
         → Cone (funcComp (M ^opF) (CDiag i)) (M .F-ob (CVtx i))
  MCCone M i = F-cone (M ^opF) (CCone i)

  preservesLCone : (M : Functor ind E) (i : LIdx) → Type _
  preservesLCone M i = isLimCone _ _ (MLCone M i)

  preservesCCone : (M : Functor ind E) (i : CIdx) → Type _
  preservesCCone M i = isLimCone {C = E ^op} _ _ (MCCone M i)

  isModel : Functor ind E → Type _
  isModel M = (∀ i → preservesLCone M i) × (∀ i → preservesCCone M i)

  isPropIsModel : (M : Functor ind E) → isProp (isModel M)
  isPropIsModel M =
    isProp× (isPropΠ (λ i → isPropIsLimCone _ _ (MLCone M i)))
            (isPropΠ (λ i → isPropIsLimCone _ _ (MCCone M i)))

  Model : Type _
  Model = Σ[ M ∈ Functor ind E ] isModel M

  -- Since `isModel` is a proposition, the category of models is
  -- literally the full subcategory of the functor category spanned by
  -- the models: a morphism of models is just a natural transformation
  -- of the underlying functors.
  MODEL : Category _ _
  MODEL = FullSubcategory (FUNCTOR ind E) isModel

  -- the forgetful functor to the functor category is fully faithful
  ModelInclusion : Functor MODEL (FUNCTOR ind E)
  ModelInclusion = FullInclusion (FUNCTOR ind E) isModel

  isFullyFaithfulModelInclusion : isFullyFaithful ModelInclusion
  isFullyFaithfulModelInclusion = isFullyFaithfulIncl (FUNCTOR ind E) isModel

-- Composing a model with a functor.  `isModel` is stated for an
-- arbitrary functor into an arbitrary category, so `isModel S E' (G ∘F M)`
-- is immediately meaningful.  The only friction is that `funcComp` is
-- not definitionally associative (its `F-id`/`F-seq` fields differ), so
-- the designated cones of `G ∘F M` agree with the `G`-images of those
-- of `M` only up to `F-assoc`.  These lemmas record that comparison.
module _ {ℓE ℓE' ℓE'' ℓE''' : Level}
         (S : Sketch ℓS ℓS' ℓLI ℓLJ ℓLJ' ℓCI ℓCJ ℓCJ')
         {E : Category ℓE ℓE'} {E' : Category ℓE'' ℓE'''}
         (G : Functor E E') (M : Functor (Sketch.ind S) E) where
  open Sketch S

  LDiag∘ : (i : LIdx)
         → funcComp G (funcComp M (LDiag i))
         ≡ funcComp (funcComp G M) (LDiag i)
  LDiag∘ i = F-assoc {F = LDiag i} {G = M} {H = G}

  MLCone∘ : (i : LIdx)
          → PathP (λ j → Cone (LDiag∘ i j) (G .F-ob (M .F-ob (LVtx i))))
                  (F-cone G (MLCone S E M i))
                  (MLCone S E' (funcComp G M) i)
  MLCone∘ i = conePathPDiag (λ v → refl)

  CDiag∘ : (i : CIdx)
         → funcComp (G ^opF) (funcComp (M ^opF) (CDiag i))
         ≡ funcComp ((funcComp G M) ^opF) (CDiag i)
  CDiag∘ i = Functor≡ (λ _ → refl) (λ _ → refl)

  MCCone∘ : (i : CIdx)
          → PathP (λ j → Cone (CDiag∘ i j) (G .F-ob (M .F-ob (CVtx i))))
                  (F-cone (G ^opF) (MCCone S E M i))
                  (MCCone S E' (funcComp G M) i)
  MCCone∘ i = conePathPDiag (λ v → refl)
