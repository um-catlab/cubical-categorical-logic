{-# OPTIONS --lossy-unification #-}
{-

  THE FIBRE OF A FORDED DISPLAYED CATEGORY.

  Compare Cubical.Categories.Instances.Fiber, which builds the same
  category out of a stock `Categoryᴰ`.  There, every operation has to
  be `reind`ed --- `fⱽ ⋆ᴰ gⱽ` lives over `id ⋆ id`, not over `id` ---
  and consequently every law has to be `rectify`d back.

  With `Categoryᶠᴰ` nothing bends.  `⋆ᴰ` takes the composite's base
  hom as a PARAMETER together with a witness, so the fibre's
  composition asks for its result over `C.id` directly, handing over
  the ford `C.id ⋆ C.id Eq.≡ C.id`.  The three category laws are then
  the displayed category's own law fields applied at that ford: not
  one `reind`, `rectify`, `subst` or `transport` appears in the
  construction below.

  The same holds for the four mixed compositions (`⋆ᴰⱽ`, `⋆ⱽᴰ`) and
  all five of their associativities, which in Fiber.agda are five-step
  `≡out`/`reind-filler` chains and here are single field applications.
  `⋆Assocᴰⱽᴰ` and `⋆Assocⱽᴰᴰ` additionally become HOMOGENEOUS
  equations rather than the `∫≡` of Fiber.agda, because the composite
  is pinned to `f ⋆ h` on both sides instead of being rebuilt.

  The fords are Eq-valued, so the ONE ford that is `Eq.refl` --- the
  fibre's identity --- computes away entirely; see `agree-id` at the
  bottom.

-}
module Cubical.Categories.Instances.Fiber.Forded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.More
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Functors.Strict.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Forded
open import Cubical.Categories.Instances.Fiber using (fiber)

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module Fibersᶠ {C : Category ℓC ℓC'} (Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
  module Cᴰ = Categoryᶠᴰ Cᴰ
  open Cᴰ public

  private
    -- THE FORDS, named once.  Each is used both in an operation and
    -- in the field that discharges it, so the two sides match on the
    -- nose and no coherence is needed.
    lId≡ : ∀ {x y} (f : C [ x , y ]) → C.id C.⋆ f Eq.≡ f
    lId≡ f = Eq.pathToEq (C.⋆IdL f)

    rId≡ : ∀ {x y} (f : C [ x , y ]) → f C.⋆ C.id Eq.≡ f
    rId≡ f = Eq.pathToEq (C.⋆IdR f)

    idL≡ : ∀ {x} → C.id {x} C.⋆ C.id {x} Eq.≡ C.id {x}
    idL≡ = lId≡ C.id

  v[_] : C.ob → Category ℓCᴰ ℓCᴰ'
  v[ x ] .Category.ob = ob[ x ]
  v[ x ] .Category.Hom[_,_] = Hom[ C.id ][_,_]
  v[ x ] .Category.id = idᴰ C.id Eq.refl
  v[ x ] .Category._⋆_ fⱽ gⱽ = ⋆ᴰ C.id C.id C.id idL≡ fⱽ gⱽ
  v[ x ] .Category.⋆IdL fⱽ = ⋆IdLᴰ C.id Eq.refl C.id idL≡ fⱽ
  v[ x ] .Category.⋆IdR fⱽ = ⋆IdRᴰ C.id C.id Eq.refl idL≡ fⱽ
  v[ x ] .Category.⋆Assoc fⱽ gⱽ hⱽ =
    ⋆Assocᴰ C.id C.id C.id C.id idL≡ C.id idL≡ C.id idL≡ idL≡ fⱽ gⱽ hⱽ
  v[ x ] .Category.isSetHom = isSetHomᴰ

  idⱽ : ∀ {x} {xᴰ : ob[ x ]} → v[ x ] [ xᴰ , xᴰ ]
  idⱽ = idᴰ C.id Eq.refl

  _⋆ⱽ_ : ∀ {x} {xᴰ xᴰ' xᴰ'' : ob[ x ]}
    → v[ x ] [ xᴰ , xᴰ' ] → v[ x ] [ xᴰ' , xᴰ'' ] → v[ x ] [ xᴰ , xᴰ'' ]
  _⋆ⱽ_ = v[ _ ] .Category._⋆_

  private
    variable
      x y z : C.ob
      xᴰ xᴰ' xᴰ'' yᴰ yᴰ' yᴰ'' zᴰ : ob[ x ]
      f g h : C [ x , y ]
      fᴰ fᴰ' gᴰ gᴰ' hᴰ hᴰ' : Hom[ f ][ xᴰ , yᴰ ]
      fⱽ fⱽ' gⱽ gⱽ' hⱽ hⱽ' : v[ x ] [ xᴰ , xᴰ' ]

  ⋆IdLⱽ : idⱽ ⋆ⱽ fⱽ ≡ fⱽ
  ⋆IdLⱽ = v[ _ ] .Category.⋆IdL _

  ⋆IdRⱽ : fⱽ ⋆ⱽ idⱽ ≡ fⱽ
  ⋆IdRⱽ = v[ _ ] .Category.⋆IdR _

  ⋆Assocⱽ : (fⱽ ⋆ⱽ gⱽ) ⋆ⱽ hⱽ ≡ fⱽ ⋆ⱽ (gⱽ ⋆ⱽ hⱽ)
  ⋆Assocⱽ = v[ _ ] .Category.⋆Assoc _ _ _

  isSetHomⱽ : isSet (v[ x ] [ xᴰ , xᴰ' ])
  isSetHomⱽ = isSetHomᴰ

  -- ----------------------------------------------------------------
  -- MIXED COMPOSITION.  A displayed hom over `f` postcomposed with a
  -- vertical one stays over `f`: the ford is `rId≡ f`, and nothing is
  -- reindexed.

  _⋆ᴰⱽ_ : Hom[ f ][ xᴰ , yᴰ ] → v[ y ] [ yᴰ , yᴰ' ] → Hom[ f ][ xᴰ , yᴰ' ]
  _⋆ᴰⱽ_ {f = f} fᴰ gⱽ = ⋆ᴰ f C.id f (rId≡ f) fᴰ gⱽ

  _⋆ⱽᴰ_ : v[ x ] [ xᴰ , xᴰ' ] → Hom[ f ][ xᴰ' , yᴰ ] → Hom[ f ][ xᴰ , yᴰ ]
  _⋆ⱽᴰ_ {f = f} fⱽ gᴰ = ⋆ᴰ C.id f f (lId≡ f) fⱽ gᴰ

  ⋆IdLᴰⱽ : idⱽ ⋆ᴰⱽ fⱽ ≡ fⱽ
  ⋆IdLᴰⱽ = ⋆IdLᴰ C.id Eq.refl C.id (rId≡ C.id) _

  ⋆IdRᴰⱽ : ∀ (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → fᴰ ⋆ᴰⱽ idⱽ ≡ fᴰ
  ⋆IdRᴰⱽ {f = f} fᴰ = ⋆IdRᴰ f C.id Eq.refl (rId≡ f) fᴰ

  ⋆IdLⱽᴰ : ∀ (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → idⱽ ⋆ⱽᴰ fᴰ ≡ fᴰ
  ⋆IdLⱽᴰ {f = f} fᴰ = ⋆IdLᴰ C.id Eq.refl f (lId≡ f) fᴰ

  ⋆IdRⱽᴰ : ∀ (fⱽ : v[ x ] [ xᴰ , xᴰ' ]) → fⱽ ⋆ⱽᴰ idⱽ ≡ fⱽ
  ⋆IdRⱽᴰ fⱽ = ⋆IdRᴰ C.id C.id Eq.refl (lId≡ C.id) fⱽ

  -- ----------------------------------------------------------------
  -- THE FIVE MIXED ASSOCIATIVITIES.  Each is `⋆Assocᴰ` at the fords
  -- the two sides already use; in Fiber.agda each is a five-step
  -- reind-filler chain wrapped in `rectify`.

  ⋆Assocᴰⱽⱽ : ∀ (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
    (gⱽ : v[ y ] [ yᴰ , yᴰ' ]) (hⱽ : v[ y ] [ yᴰ' , yᴰ'' ])
    → (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰⱽ hⱽ ≡ fᴰ ⋆ᴰⱽ (gⱽ ⋆ⱽ hⱽ)
  ⋆Assocᴰⱽⱽ {f = f} fᴰ gⱽ hⱽ =
    ⋆Assocᴰ f C.id C.id f (rId≡ f) C.id idL≡
      f (rId≡ f) (rId≡ f) fᴰ gⱽ hⱽ

  ⋆Assocⱽⱽᴰ : ∀ (fⱽ : v[ x ] [ xᴰ , xᴰ' ]) (gⱽ : v[ x ] [ xᴰ' , xᴰ'' ])
    (hᴰ : Hom[ f ][ xᴰ'' , yᴰ ])
    → (fⱽ ⋆ⱽ gⱽ) ⋆ⱽᴰ hᴰ ≡ fⱽ ⋆ⱽᴰ (gⱽ ⋆ⱽᴰ hᴰ)
  ⋆Assocⱽⱽᴰ {f = f} fⱽ gⱽ hᴰ =
    ⋆Assocᴰ C.id C.id f C.id idL≡ f (lId≡ f)
      f (lId≡ f) (lId≡ f) fⱽ gⱽ hᴰ

  ⋆Assocⱽᴰⱽ : ∀ (fⱽ : v[ x ] [ xᴰ , xᴰ' ]) (gᴰ : Hom[ g ][ xᴰ' , yᴰ ])
    (hⱽ : v[ y ] [ yᴰ , yᴰ' ])
    → (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰⱽ hⱽ ≡ fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰⱽ hⱽ)
  ⋆Assocⱽᴰⱽ {g = g} fⱽ gᴰ hⱽ =
    ⋆Assocᴰ C.id g C.id g (lId≡ g) g (rId≡ g)
      g (rId≡ g) (lId≡ g) fⱽ gᴰ hⱽ

  -- HOMOGENEOUS, unlike Fiber.agda's `∫⋆Assocᴰⱽᴰ`/`⋆Assocⱽᴰᴰ`: the
  -- outer composite is pinned to `f ⋆ h` on both sides.
  ⋆Assocᴰⱽᴰ : ∀ (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gⱽ : v[ y ] [ yᴰ , yᴰ' ])
    (hᴰ : Hom[ h ][ yᴰ' , zᴰ ])
    → ⋆ᴰ f h (f C.⋆ h) Eq.refl (fᴰ ⋆ᴰⱽ gⱽ) hᴰ
      ≡ ⋆ᴰ f h (f C.⋆ h) Eq.refl fᴰ (gⱽ ⋆ⱽᴰ hᴰ)
  ⋆Assocᴰⱽᴰ {f = f} {h = h} fᴰ gⱽ hᴰ =
    ⋆Assocᴰ f C.id h f (rId≡ f) h (lId≡ h)
      (f C.⋆ h) Eq.refl Eq.refl fᴰ gⱽ hᴰ

  ⋆Assocⱽᴰᴰ : ∀ (fⱽ : v[ x ] [ xᴰ , xᴰ' ]) (gᴰ : Hom[ g ][ xᴰ' , yᴰ ])
    (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
    → ⋆ᴰ g h (g C.⋆ h) Eq.refl (fⱽ ⋆ⱽᴰ gᴰ) hᴰ
      ≡ fⱽ ⋆ⱽᴰ ⋆ᴰ g h (g C.⋆ h) Eq.refl gᴰ hᴰ
  ⋆Assocⱽᴰᴰ {g = g} {h = h} fⱽ gᴰ hᴰ =
    ⋆Assocᴰ C.id g h g (lId≡ g) (g C.⋆ h) Eq.refl
      (g C.⋆ h) Eq.refl (lId≡ (g C.⋆ h)) fⱽ gᴰ hᴰ

  -- ----------------------------------------------------------------
  -- Hom[ f ] as a profunctor between the two fibres it connects.
  open NatTrans
  HomᴰProf : (f : C [ x , y ]) → Profunctor v[ y ] v[ x ] ℓCᴰ'
  HomᴰProf f .Functor.F-ob yᴰ .Functor.F-ob xᴰ .fst = Hom[ f ][ xᴰ , yᴰ ]
  HomᴰProf f .Functor.F-ob yᴰ .Functor.F-ob xᴰ .snd = isSetHomᴰ
  HomᴰProf f .Functor.F-ob yᴰ .Functor.F-hom gⱽ fᴰ = gⱽ ⋆ⱽᴰ fᴰ
  HomᴰProf f .Functor.F-ob yᴰ .Functor.F-id = funExt ⋆IdLⱽᴰ
  HomᴰProf f .Functor.F-ob yᴰ .Functor.F-seq hⱽ gⱽ =
    funExt λ fᴰ → ⋆Assocⱽⱽᴰ gⱽ hⱽ fᴰ
  HomᴰProf f .Functor.F-hom gⱽ .N-ob x fᴰ = fᴰ ⋆ᴰⱽ gⱽ
  HomᴰProf f .Functor.F-hom gⱽ .N-hom fⱽ =
    funExt λ hᴰ → ⋆Assocⱽᴰⱽ fⱽ hᴰ gⱽ
  HomᴰProf f .Functor.F-id =
    makeNatTransPath (funExt λ _ → funExt ⋆IdRᴰⱽ)
  HomᴰProf f .Functor.F-seq gⱽ hⱽ = makeNatTransPath
    (funExt λ _ → funExt λ fᴰ → sym (⋆Assocᴰⱽⱽ fᴰ gⱽ hⱽ))

  -- ----------------------------------------------------------------
  -- THE FIBRE INCLUSION, as a STRICT functor into the total category.
  -- With the fords oriented forwards `F-id` is a bare `Eq.ap`; there
  -- is no counterpart in Fiber.agda.
  open StrictFunctor
  ιᶠ : (x : C.ob) → StrictFunctor v[ x ] (∫ᶠ Cᴰ)
  ιᶠ x .F-ob xᴰ = x , xᴰ
  ιᶠ x .F-hom fⱽ = C.id , fⱽ
  ιᶠ x .F-id fⱽ e = Eq.ap (λ u → C.id , u) e
  ιᶠ x .F-seq fⱽ gⱽ hⱽ e = Eq.pathToEq (ΣPathP (C.⋆IdL C.id ,
    ⋆ᴰ-coh C.id C.id (C.id C.⋆ C.id) C.id Eq.refl idL≡
      (C.⋆IdL C.id) fⱽ gⱽ
    ▷ Eq.eqToPath e))

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᶠᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  fiberᶠ : C .ob → Category ℓCᴰ ℓCᴰ'
  fiberᶠ x = Fibersᶠ.v[_] Cᴰ x

-- ------------------------------------------------------------------
-- HOW IT LINES UP WITH Cubical.Categories.Instances.Fiber.  Running a
-- stock `Categoryᴰ` through `fromCategoryᴰ` and then through the
-- fibre above reproduces Fiber.agda's `fiber` on objects, on homs,
-- and --- this is what the Eq-valued ford buys --- on the IDENTITY,
-- all three by `refl`: `fromCategoryᴰ`'s `idᴰ` at the ford `Eq.refl`
-- is `Eq.transport _ Eq.refl Cᴰ.idᴰ`, which COMPUTES to `Cᴰ.idᴰ`.
-- (Under the earlier Path-valued ford this was a stuck `subst _ refl`
-- and the statement was not provable by `refl` at all.)
--
-- Composition agrees only up to the difference between
-- `Eq.transport P (Eq.pathToEq p)` and `subst P p`, since the ford
-- there is a genuine law rather than `Eq.refl`.  That is a conversion
-- lemma, not a coherence: no rectification is involved.
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  private module Cᴰ = Categoryᴰ Cᴰ

  agree-ob : ∀ x → fiberᶠ (fromCategoryᴰ Cᴰ) x .ob ≡ fiber Cᴰ x .ob
  agree-ob x = refl

  agree-Hom : ∀ x → fiberᶠ (fromCategoryᴰ Cᴰ) x .Hom[_,_]
                  ≡ fiber Cᴰ x .Hom[_,_]
  agree-Hom x = refl

  -- NEW, and the point of the Eq ford: the identity now computes.
  agree-id : ∀ x (xᴰ : Cᴰ.ob[ x ])
    → Category.id (fiberᶠ (fromCategoryᴰ Cᴰ) x) {xᴰ}
      ≡ Category.id (fiber Cᴰ x) {xᴰ}
  agree-id x xᴰ = refl

  -- `reind` is sealed in an `opaque` block in Cubical.Foundations.More,
  -- so this one needs the seal broken to see it as `subst`.
  opaque
    unfolding depReasoning.reind
    agree-⋆ : ∀ x (xᴰ yᴰ zᴰ : Cᴰ.ob[ x ])
      (fⱽ : fiber Cᴰ x [ xᴰ , yᴰ ]) (gⱽ : fiber Cᴰ x [ yᴰ , zᴰ ])
      → Category._⋆_ (fiberᶠ (fromCategoryᴰ Cᴰ) x) fⱽ gⱽ
        ≡ Category._⋆_ (fiber Cᴰ x) fⱽ gⱽ
    agree-⋆ x xᴰ yᴰ zᴰ fⱽ gⱽ = Eq.eqToPath
      (Eq.transportPathToEq→transportPath
        (λ i → Cᴰ.Hom[ i ][ xᴰ , zᴰ ])
        (⋆IdL C (id C))
        (Cᴰ._⋆ᴰ_ fⱽ gⱽ))

-- ------------------------------------------------------------------
-- STRICTNESS IS TRANSMITTED.  Because every law of `v[ x ]` above is
-- the corresponding field of `Cᴰ` --- not a chain reassembled around
-- it --- the fibre of a displayed category with `refl` laws has
-- `refl` laws.  Here is a witness: grade C by the endofunction monoid
-- of a set, whose unit and associativity are definitional.  The
-- fibre's composition then satisfies all three laws by `refl`.
--
-- The stock construction cannot do this at any Cᴰ whatsoever: its
-- composite is `reind (C.⋆IdL C.id) (fⱽ ⋆ᴰ gⱽ)`, so `idⱽ ⋆ⱽ fⱽ` is a
-- stuck `transp` no matter how strict `⋆ᴰ` is.
module StrictnessTransmitted {C : Category ℓC ℓC'} (A : hSet ℓCᴰ') where
  open Categoryᶠᴰ

  Endoᶠᴰ : Categoryᶠᴰ C ℓ-zero ℓCᴰ'
  Endoᶠᴰ .ob[_] _ = Unit
  Endoᶠᴰ .Hom[_][_,_] _ _ _ = A .fst → A .fst
  Endoᶠᴰ .idᴰ i ei a = a
  Endoᶠᴰ .⋆ᴰ f g h e u v a = v (u a)
  Endoᶠᴰ .⋆IdLᴰ i ei f e fᴰ = refl
  Endoᶠᴰ .⋆IdRᴰ f i ei e fᴰ = refl
  Endoᶠᴰ .⋆Assocᴰ f g h fg efg gh egh k e₁ e₂ fᴰ gᴰ hᴰ = refl
  Endoᶠᴰ .idᴰ-coh i i' ei ei' p = refl
  Endoᶠᴰ .⋆ᴰ-coh f g h h' e e' p fᴰ gᴰ = refl
  Endoᶠᴰ .isSetHomᴰ = isSetΠ λ _ → A .snd

  private module F = Fibersᶠ Endoᶠᴰ

  module _ (x : Category.ob C) where
    private
      open module Fx = Category (F.v[ x ]) using () renaming
        (id to 1ⱽ; _⋆_ to _⊙_)

    module _ (fⱽ gⱽ hⱽ : F.v[ x ] [ tt , tt ]) where
      endo-⋆IdL : 1ⱽ ⊙ fⱽ ≡ fⱽ
      endo-⋆IdL = refl

      endo-⋆IdR : fⱽ ⊙ 1ⱽ ≡ fⱽ
      endo-⋆IdR = refl

      endo-⋆Assoc : (fⱽ ⊙ gⱽ) ⊙ hⱽ ≡ fⱽ ⊙ (gⱽ ⊙ hⱽ)
      endo-⋆Assoc = refl
