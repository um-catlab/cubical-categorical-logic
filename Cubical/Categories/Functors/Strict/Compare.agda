-- Measuring what `StrictFunctor` buys over `Functor`.
--
-- `Cubical/Algebra/Sketch/Base.agda` has to ship four comparison
-- paths (`LDiag∘`, `MLCone∘`, `CDiag∘`, `MCCone∘`) whose only reason
-- to exist is that `funcComp` is not definitionally associative: its
-- `F-id`/`F-seq` fields are built with `_∙_`, and `Functor` is
-- `no-eta-equality`.  This file mirrors exactly that situation with
-- both notions of functor, side by side, so the difference is
-- measured rather than asserted.
--
-- Summary of the measurements (each `refl` below typechecks):
--
--   * `(H S∘ G) S∘ F ≡ H S∘ (G S∘ F)`   is  refl
--   * `SId S∘ F ≡ F` and `F S∘ SId ≡ F` are refl
--   * the corresponding `∘F` statements are NOT refl; see the
--     verbatim errors recorded in the comments below.
module Cubical.Categories.Functors.Strict.Compare where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Limits.Limits

open import Cubical.Categories.Functors.Strict.Base

open Category
open Functor
open StrictFunctor

private
  variable
    ℓJ ℓJ' ℓI ℓI' ℓE ℓE' ℓE'' ℓE''' : Level

------------------------------------------------------------------------
-- 1.  The strict side: associativity and unit are `refl`.
------------------------------------------------------------------------

-- These restate the tests already living in `Strict.Base`, so that the
-- positive and the negative measurement sit next to each other.

module _ {B : Category ℓJ ℓJ'} {C : Category ℓI ℓI'}
         {D : Category ℓE ℓE'} {E : Category ℓE'' ℓE'''} where

  S∘-assoc-is-refl : (F : StrictFunctor B C) (G : StrictFunctor C D)
                     (H : StrictFunctor D E)
                   → ((H S∘ G) S∘ F) ≡ (H S∘ (G S∘ F))
  S∘-assoc-is-refl F G H = refl

module _ {C : Category ℓJ ℓJ'} {D : Category ℓI ℓI'} where

  S∘-lUnit-is-refl : (F : StrictFunctor C D) → (SId S∘ F) ≡ F
  S∘-lUnit-is-refl F = refl

  S∘-rUnit-is-refl : (F : StrictFunctor C D) → (F S∘ SId) ≡ F
  S∘-rUnit-is-refl F = refl

------------------------------------------------------------------------
-- 2.  The ordinary side: the same statements are NOT `refl`.
------------------------------------------------------------------------

-- Replacing `F-assoc` by `refl` in `∘F-assoc` below fails with:
--
--   error: [UnequalTerms]
--   The terms
--     funcComp {D = C} (H ∘F G) F
--   and
--     funcComp {D = D} H (G ∘F F)
--   are not equal at type Functor B E
--   when checking that the expression refl has type
--   (H ∘F G) ∘F F ≡ H ∘F G ∘F F
--
-- Likewise `𝟙⟨ D ⟩ ∘F F ≡ F` by `refl` fails with:
--
--   error: [UnequalTerms]
--   The terms
--     funcComp 𝟙⟨ D ⟩ F
--   and
--     F
--   are not equal at type Functor C D
--   when checking that the expression refl has type 𝟙⟨ D ⟩ ∘F F ≡ F
--
-- The cause is visible in `funcComp`'s definition:
--
--   (funcComp G F) .F-id      = cong (G ⟪_⟫) (F .F-id) ∙ G .F-id
--   (funcComp G F) .F-seq f g = cong (G ⟪_⟫) (F .F-seq _ _) ∙ G .F-seq _ _
--
-- `_∙_` is an `hcomp`, so neither `refl ∙ p ≡ p` nor associativity of
-- `_∙_` holds definitionally; and `Functor` is `no-eta-equality`, so a
-- record path is never `refl` even when all fields agree.
--
-- `StrictFunctor` avoids both problems at once.  It has eta, and its
-- forded `F-id`/`F-seq` take the equation as an *argument* rather than
-- proving it with `_∙_`, so `_S∘_` merely reassociates `sym`s:
--
--   ((H S∘ G) S∘ F) .F-seq f g h e
--     = H.F-seq _ _ _ (sym (G.F-seq _ _ _ (sym (F.F-seq f g h e))))
--   (H S∘ (G S∘ F)) .F-seq f g h e
--     = H.F-seq _ _ _ (sym (G.F-seq _ _ _ (sym (F.F-seq f g h e))))
--
-- — literally the same term.  For the unit laws the obligation is
-- `sym (sym p) ≡ p`, which is definitional in cubical Agda because
-- `~ ~ i` reduces to `i`.

module _ {B : Category ℓJ ℓJ'} {C : Category ℓI ℓI'}
         {D : Category ℓE ℓE'} {E : Category ℓE'' ℓE'''} where

  ∘F-assoc : (F : Functor B C) (G : Functor C D) (H : Functor D E)
           → ((H ∘F G) ∘F F) ≡ (H ∘F (G ∘F F))
  ∘F-assoc F G H = sym (F-assoc {F = F} {G = G} {H = H})

------------------------------------------------------------------------
-- 3.  Mirroring `LDiag∘` / `MLCone∘`.
------------------------------------------------------------------------

-- The sketch situation verbatim: a diagram `Dg : Functor J ind`, a
-- model `M : Functor ind E`, and a functor `G : Functor E E'` along
-- which the model is pushed forward.  `Sketch.Base` needs
--
--   LDiag∘ : G ∘F (M ∘F Dg) ≡ (G ∘F M) ∘F Dg
--
-- purely so that the designated cones of the two groupings can be
-- compared, which forces `MLCone∘` to be a `PathP` over `LDiag∘`
-- rather than a path.

module _ {J : Category ℓJ ℓJ'} {ind : Category ℓI ℓI'}
         {E : Category ℓE ℓE'} {E' : Category ℓE'' ℓE'''}
         (Dg : Functor J ind) (M : Functor ind E) (G : Functor E E')
         where

  -- This is `LDiag∘` itself, with the sketch's own proof term.
  LDiag∘-mirror : G ∘F (M ∘F Dg) ≡ (G ∘F M) ∘F Dg
  LDiag∘-mirror = F-assoc {F = Dg} {G = M} {H = G}

  -- Because `LDiag∘-mirror` is not `refl`, the two groupings give
  -- *different types* of cone, and a cone for one reaches the other
  -- only by a genuine `subst`.  This is the cost the sketch pays.
  ∘F-coneTransport : {v : ob E'}
                   → Cone (G ∘F (M ∘F Dg)) v
                   → Cone ((G ∘F M) ∘F Dg) v
  ∘F-coneTransport {v} = subst (λ F → Cone F v) LDiag∘-mirror

  -- And `MLCone∘`'s shape: a PathP over the comparison, not a path.
  MLCone∘-shape : {v : ob E'}
                → Cone (G ∘F (M ∘F Dg)) v
                → Cone ((G ∘F M) ∘F Dg) v
                → Type (ℓ-max (ℓ-max ℓJ ℓJ') ℓE''')
  MLCone∘-shape {v} x y = PathP (λ j → Cone (LDiag∘-mirror j) v) x y

module _ {J : Category ℓJ ℓJ'} {ind : Category ℓI ℓI'}
         {E : Category ℓE ℓE'} {E' : Category ℓE'' ℓE'''}
         (Dg : StrictFunctor J ind) (M : StrictFunctor ind E)
         (G : StrictFunctor E E')
         where

  -- The strict analogue of `LDiag∘`.  It is `refl`.
  LDiag∘-strict : G S∘ (M S∘ Dg) ≡ (G S∘ M) S∘ Dg
  LDiag∘-strict = refl

  -- Consequently the two cone types are *the same type*, and the
  -- transport above is replaced by the identity function.  Note that
  -- the two `Cone` arguments below are written with different
  -- groupings and Agda accepts `λ c → c` between them.
  S∘-coneNoTransport : {v : ob E'}
                     → Cone (Strict→Fun (G S∘ (M S∘ Dg))) v
                     → Cone (Strict→Fun ((G S∘ M) S∘ Dg)) v
  S∘-coneNoTransport c = c

  -- And `MLCone∘`'s PathP degenerates definitionally to a plain path:
  -- the `refl` below is a path between *types*, witnessing that no
  -- `PathP` machinery is needed at all.
  MLCone∘-degenerates :
    {v : ob E'}
    (x y : Cone (Strict→Fun ((G S∘ M) S∘ Dg)) v)
    → (PathP (λ j → Cone (Strict→Fun (LDiag∘-strict j)) v) x y)
    ≡ (x ≡ y)
  MLCone∘-degenerates x y = refl

------------------------------------------------------------------------
-- 4.  Relating the two notions.
------------------------------------------------------------------------

-- `Strict→Fun` and `Fun→Strict` live in `Strict.Base`.  Neither round
-- trip is `refl`.
--
-- `Strict→Fun (Fun→Strict F) ≡ F` by `refl` fails with:
--
--   error: [UnequalTerms]
--   The terms
--     Strict→Fun (Fun→Strict F)
--   and
--     F
--   are not equal at type Functor C D
--   when checking that the expression refl has type
--   Strict→Fun (Fun→Strict F) ≡ F
--
-- (`Functor` is `no-eta-equality`, so this could not have been `refl`
-- regardless of the fields.)
--
-- `Fun→Strict (Strict→Fun F) ≡ F` by `refl` fails with:
--
--   error: [UnequalTerms]
--   The terms
--     hcomp
--     (doubleComp-faces (λ _ → Strict→Fun F .Functor.F-hom f)
--      (Strict→Fun F .Functor.F-id) i)
--     (Strict→Fun F .Functor.F-hom (x (~ i)))
--   and
--     F .StrictFunctor.F-id f x i
--   are not equal at type ...
--
-- Note that eta *did* fire for `StrictFunctor` here: Agda reduced the
-- record comparison all the way down to a comparison of the `F-id`
-- fields, and the only obstruction is the `hcomp` that `Fun→Strict`
-- introduces via `_∙_`.  This is exactly the asymmetry being measured:
-- `StrictFunctor` has eta, `Functor` does not.
--
-- Both round trips do hold propositionally, since the obstructions all
-- live in hom-sets.

module _ {C : Category ℓJ ℓJ'} {D : Category ℓI ℓI'} where

  Strict→Fun→Strict : (F : Functor C D) → Strict→Fun (Fun→Strict F) ≡ F
  Strict→Fun→Strict F = Functor≡ (λ _ → refl) (λ _ → refl)

  Fun→Strict→Fun : (F : StrictFunctor C D) → Fun→Strict (Strict→Fun F) ≡ F
  Fun→Strict→Fun F i .F-ob = F .F-ob
  Fun→Strict→Fun F i .F-hom = F .F-hom
  Fun→Strict→Fun F i .F-id f e =
    isSetHom D _ _ (Fun→Strict (Strict→Fun F) .F-id f e) (F .F-id f e) i
  Fun→Strict→Fun F i .F-seq f g h e =
    isSetHom D _ _ (Fun→Strict (Strict→Fun F) .F-seq f g h e)
               (F .F-seq f g h e) i

  -- The translation is compatible with composition, propositionally.
  Strict→Fun-pres-S∘ :
    {B : Category ℓE ℓE'}
    (F : StrictFunctor B C) (G : StrictFunctor C D)
    → Strict→Fun (G S∘ F) ≡ (Strict→Fun G ∘F Strict→Fun F)
  Strict→Fun-pres-S∘ F G = Functor≡ (λ _ → refl) (λ _ → refl)

  Strict→Fun-pres-SId : Strict→Fun (SId {C = C}) ≡ 𝟙⟨ C ⟩
  Strict→Fun-pres-SId = Functor≡ (λ _ → refl) (λ _ → refl)
