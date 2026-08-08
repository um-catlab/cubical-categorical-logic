{-
  STRICT FUNCTORS, locally small.

  The level-indexed counterpart of
  Cubical.Categories.Functors.Strict.Base.  The laws are FORDED:
  rather than `F ⟪ id ⟫ ≡ id`, the field takes ANY `f` together with a
  witness `id ≡ f`.  Composition then passes the ford along instead of
  building a `_∙_` chain, and `_S∘_` is definitionally unital and
  associative FOR VARIABLES -- which `LocallySmall.Functor._∘F_` is
  not, since its `F-id` is `cong (F .F-hom) (G .F-id) ∙ F .F-id`.

  ORIENTATION, and why it matters.  The fords are `Eq`-valued and
  point FORWARDS, in the same direction the displayed category's
  `idᴰ`/`⋆ᴰ` want them.  That is what lets `_S∘_` and `reindexS` hand
  the witness over verbatim, with no `sym` anywhere.  An earlier
  version had `F-id : C.id ≡ f → F-hom f ≡ D.id`, opposite to
  `Categoryᶠᴰ.idᴰ`, so reindexing had to `sym`; `sym (sym e)` is
  definitional only for Path, which forced a Path-valued ford, whose
  `subst B refl b` is STUCK for neutral `B`.  With the fords aligned
  the ford can be `Eq`, and `Eq.transport C Eq.refl b` REDUCES to `b`
  -- so strictness at variables and computation at `refl` come
  together.

  `LocallySmall.Functor` already has `no-eta-equality` commented out, so
  eta -- which is what makes two records with definitionally equal
  fields definitionally equal -- is available here too.  Do not add it.

  NOTE ON TESTING.  At Typeω you cannot state `x ≡ y`, since Path is
  Type-valued.  Definitional equality is therefore witnessed by
  COERCION: `Coe x y` below is inhabited by the identity exactly when
  x and y are definitionally equal.
-}
module Cubical.Categories.LocallySmall.Functor.Strict where

open import Cubical.Foundations.Prelude

import Cubical.Data.Equality as Eq

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Variables.Base

record StrictFunctor
  (C : Category Cob CHom-ℓ) (D : Category Dob DHom-ℓ) : Typeω where
  -- eta-equality is the DEFAULT and is load-bearing.  Do not add
  -- no-eta-equality.
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
  field
    F-ob : Cob → Dob
    F-hom : ∀ {x y} → C.Hom[ x , y ] → D.Hom[ F-ob x , F-ob y ]
    F-id : ∀ {x} (f : C.Hom[ x , x ]) → C.id Eq.≡ f → D.id Eq.≡ F-hom f
    F-seq : ∀ {x y z}
      (f : C.Hom[ x , y ]) (g : C.Hom[ y , z ]) (h : C.Hom[ x , z ])
      → f C.⋆ g Eq.≡ h → (F-hom f D.⋆ F-hom g) Eq.≡ F-hom h

open StrictFunctor

SId : {C : Category Cob CHom-ℓ} → StrictFunctor C C
SId .F-ob = λ z → z
SId .F-hom = λ z → z
SId .F-id f e = e
SId .F-seq f g h e = e

_S∘_ : {C : Category Cob CHom-ℓ} {D : Category Dob DHom-ℓ}
       {E : Category Eob EHom-ℓ}
  → StrictFunctor D E → StrictFunctor C D → StrictFunctor C E
(G S∘ F) .F-ob = λ z → G .F-ob (F .F-ob z)
(G S∘ F) .F-hom = λ z → G .F-hom (F .F-hom z)
(G S∘ F) .F-id f e = G .F-id (F .F-hom f) (F .F-id f e)
(G S∘ F) .F-seq f g h e =
  G .F-seq (F .F-hom f) (F .F-hom g) (F .F-hom h) (F .F-seq f g h e)
infixr 30 _S∘_

-- ------------------------------------------------------------------
-- DEFINITIONAL EQUALITY AT Typeω, by coercion.
Coe : {A : Typeω} → A → A → Typeω₁
Coe {A} x y = (P : A → Typeω) → P x → P y

module _ {C : Category Cob CHom-ℓ} {D : Category Dob DHom-ℓ} where
  S∘-lUnit : (F : StrictFunctor C D) → Coe (SId S∘ F) F
  S∘-lUnit F P x = x

  S∘-rUnit : (F : StrictFunctor C D) → Coe (F S∘ SId) F
  S∘-rUnit F P x = x

module _ {B : Category Cob CHom-ℓ} {C : Category Dob DHom-ℓ}
  {D : Category Eob EHom-ℓ} {E : Category Eob EHom-ℓ} where
  S∘-Assoc : (F : StrictFunctor B C) (G : StrictFunctor C D)
    (H : StrictFunctor D E) → Coe ((H S∘ G) S∘ F) (H S∘ (G S∘ F))
  S∘-Assoc F G H P x = x

-- the forgetful map to the ordinary locally small functor
open import Cubical.Categories.LocallySmall.Functor.Base using (Functor)

Strict→Fun : {C : Category Cob CHom-ℓ} {D : Category Dob DHom-ℓ}
  → StrictFunctor C D → Functor C D
Strict→Fun F .Functor.F-ob = F .F-ob
Strict→Fun F .Functor.F-hom = F .F-hom
Strict→Fun F .Functor.F-id = Eq.eqToPath (Eq.sym (F .F-id _ Eq.refl))
Strict→Fun F .Functor.F-seq f g =
  Eq.eqToPath (Eq.sym (F .F-seq f g _ Eq.refl))

Fun→Strict : {C : Category Cob CHom-ℓ} {D : Category Dob DHom-ℓ}
  → Functor C D → StrictFunctor C D
Fun→Strict F .F-ob = F .Functor.F-ob
Fun→Strict F .F-hom = F .Functor.F-hom
Fun→Strict F .F-id f e = Eq.pathToEq
  (sym (F .Functor.F-id) ∙ cong (F .Functor.F-hom) (Eq.eqToPath e))
Fun→Strict F .F-seq f g h e = Eq.pathToEq
  (sym (F .Functor.F-seq f g) ∙ cong (F .Functor.F-hom) (Eq.eqToPath e))
