{-
  SMALL-FIBRE MACHINERY, FORDED.

  The forded counterpart of Displayed.Category.Small and
  Displayed.Category.SmallDisplayedFibers, over
  Displayed.Category.Forded's `Categoryᶠᴰ`.

  WHAT THE FORD BUYS, AND WHAT IT DOES NOT.

  It does NOT remove the `Id⋆Eq` witness.  A fibre morphism's base hom
  is `C.id`, so composing two of them lands over `C.id ⋆ C.id`, and
  putting it back over `C.id` needs `C.id ⋆ C.id Eq.≡ C.id` no matter
  how it is packaged.  `fibᶠ` therefore takes the same `C-⋆` argument
  `fibEq` does.  (`Eq.pathToEq (C.⋆IdL C.id)` would typecheck but does
  NOT reduce to `Eq.refl`, so it would break computation; checked.)

  It DOES remove everything else.  `fib` is
  `reindex (elimUNIT c) Cᴰ`, whose identity and composition are
  `reind`s -- transports -- which is why `fibEq` had to exist at all.
  Forded, the witness goes into the ford ARGUMENT of `⋆ᴰ`, never into
  a transport, so there is one construction rather than two.  And the
  displayed fibre `fibᶠᴰ`, which `fibᴰEq` builds as
  `reindexEq (fibᴰF ∘F fibEq→fib) Cᴰᴰ Eq.refl F-seq'`, is here a
  single transport-free `reindexS` along a strict functor whose
  `F-seq` is DERIVED from `C-⋆` -- so the `F-seq'` obligation, six
  lines of `Eq`-valued statement in the stock version, is gone, as is
  the `fibEq→fib` correction functor.

  Likewise `_×ᶠᴰ_` is direct where `_×ᴰ_` is
  `reindexEq Δ (Cᴰ ×Cᴰ Dᴰ) Eq.refl (λ _ _ → Eq.refl)`: the forded laws
  are homogeneous equations at a pinned base hom, so the product's
  laws are `ΣPathP`s of the factors' laws.

  Because the fords are `Eq`-valued and oriented forwards, all of this
  COMPUTES: `Eq.transport C Eq.refl b` reduces to `b`, so wherever the
  witnesses are `Eq.refl` the fibre's `idᴰ` and `⋆ᴰ` reduce to the
  underlying ones.  See Instances.Sets.SmallFibersForded.

  TESTING AT Typeω uses `Coe` from Functor.Strict, as elsewhere.
-}
module Cubical.Categories.LocallySmall.Displayed.Category.SmallDisplayedFibers.Forded
  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Functor.Strict
open import Cubical.Categories.LocallySmall.Variables.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Base
  using (Categoryᴰ)
open import Cubical.Categories.LocallySmall.Displayed.Category.Forded

open Category
open Categoryᶠᴰ
open StrictFunctor
open Σω
open Liftω

-- ------------------------------------------------------------------
-- THE FIBRE OF A FORDED DISPLAYED CATEGORY, directly.
module _ {C : Category Cob CHom-ℓ}
  {obᴰ : Cob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
  (Cᴰ : Categoryᶠᴰ C obᴰ Hom-ℓᴰ) where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᶠᴰ Cᴰ

  module _ (C-⋆ : C.Id⋆Eq) where

    fibᶠ : (c : Cob) → Category (obᴰ c) (Hom-ℓᴰ c c)
    fibᶠ c .Hom[_,_] xᴰ yᴰ = Cᴰ.Hom[ C.id ][ xᴰ , yᴰ ]
    fibᶠ c .id = Cᴰ.idᴰ C.id Eq.refl
    fibᶠ c ._⋆_ fᴰ gᴰ = Cᴰ.⋆ᴰ C.id C.id C.id C-⋆ fᴰ gᴰ
    fibᶠ c .⋆IdL fᴰ = Cᴰ.⋆IdLᴰ C.id Eq.refl C.id C-⋆ fᴰ
    fibᶠ c .⋆IdR fᴰ = Cᴰ.⋆IdRᴰ C.id C.id Eq.refl C-⋆ fᴰ
    fibᶠ c .⋆Assoc fᴰ gᴰ hᴰ =
      Cᴰ.⋆Assocᴰ C.id C.id C.id
        C.id C-⋆ C.id C-⋆ C.id C-⋆ C-⋆ fᴰ gᴰ hᴰ
    fibᶠ c .isSetHom = Cᴰ.isSetHomᴰ

    -- The inclusion of the fibre into the total category, as a STRICT
    -- functor.  `F-seq` is DERIVED from `C-⋆`, by matching on it; when
    -- `C-⋆` is `Eq.refl` the whole thing collapses to `Eq.ap (_ ,_)`,
    -- hence to `Eq.refl` on `Eq.refl`, hence computes downstream.
    module _ (c : Cob) where
      private
        ι-seq : ∀ {xᴰ yᴰ zᴰ : obᴰ c}
          (u : C.Hom[ c , c ]) (q : C.id C.⋆ C.id Eq.≡ u)
          (f : Cᴰ.Hom[ C.id ][ xᴰ , yᴰ ])
          (g : Cᴰ.Hom[ C.id ][ yᴰ , zᴰ ])
          (h : Cᴰ.Hom[ u ][ xᴰ , zᴰ ])
          → Cᴰ.⋆ᴰ C.id C.id u q f g Eq.≡ h
          → Eq._≡_ {A = Σ[ k ∈ C.Hom[ c , c ] ] Cᴰ.Hom[ k ][ xᴰ , zᴰ ]}
              (C.id C.⋆ C.id ,
                 Cᴰ.⋆ᴰ C.id C.id (C.id C.⋆ C.id) Eq.refl f g)
              (u , h)
        ι-seq u Eq.refl f g h Eq.refl = Eq.refl

      ιᶠ : StrictFunctor (fibᶠ c) (∫ᶠ Cᴰ)
      ιᶠ .F-ob xᴰ = c , xᴰ
      ιᶠ .F-hom fᴰ = C.id , fᴰ
      ιᶠ .F-id f e = Eq.ap (C.id ,_) e
      ιᶠ .F-seq f g h e = ι-seq C.id C-⋆ f g h e

-- ------------------------------------------------------------------
-- BACK TO A STOCK DISPLAYED CATEGORY.  `Displayed.Category.Forded`
-- has `fromCategoryᴰ`; this is the converse, so a forded construction
-- can be packaged as an ordinary `Categoryᴰ` -- and hence as a
-- `SmallCategoryᴰ` -- without redoing anything.  The proofs are
-- `∫ᶠ`'s, since `Categoryᴰ`'s laws are `∫≡`s.
module _ {C : Category Cob CHom-ℓ}
  {obᴰ : Cob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
  (Cᴰ : Categoryᶠᴰ C obᴰ Hom-ℓᴰ) where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᶠᴰ Cᴰ

  open Categoryᴰ

  toCategoryᴰ : Categoryᴰ C obᴰ Hom-ℓᴰ
  toCategoryᴰ .Hom[_][_,_] = Cᴰ.Hom[_][_,_]
  toCategoryᴰ .idᴰ = Cᴰ.idᴰ C.id Eq.refl
  toCategoryᴰ ._⋆ᴰ_ {f = f} {g = g} fᴰ gᴰ =
    Cᴰ.⋆ᴰ f g (f C.⋆ g) Eq.refl fᴰ gᴰ
  toCategoryᴰ .⋆IdLᴰ {f = f} fᴰ = ΣPathP (C.⋆IdL f ,
    (Cᴰ.⋆ᴰ-coh C.id f (C.id C.⋆ f) f Eq.refl (Eq.pathToEq (C.⋆IdL f))
       (C.⋆IdL f) (Cᴰ.idᴰ C.id Eq.refl) fᴰ)
    ▷ Cᴰ.⋆IdLᴰ C.id Eq.refl f (Eq.pathToEq (C.⋆IdL f)) fᴰ)
  toCategoryᴰ .⋆IdRᴰ {f = f} fᴰ = ΣPathP (C.⋆IdR f ,
    (Cᴰ.⋆ᴰ-coh f C.id (f C.⋆ C.id) f Eq.refl (Eq.pathToEq (C.⋆IdR f))
       (C.⋆IdR f) fᴰ (Cᴰ.idᴰ C.id Eq.refl))
    ▷ Cᴰ.⋆IdRᴰ f C.id Eq.refl (Eq.pathToEq (C.⋆IdR f)) fᴰ)
  toCategoryᴰ .⋆Assocᴰ {f = f} {g = g} {h = h} fᴰ gᴰ hᴰ =
    ΣPathP (C.⋆Assoc f g h ,
      Cᴰ.⋆Assocᴰ f g h (f C.⋆ g) Eq.refl (g C.⋆ h) Eq.refl
        ((f C.⋆ g) C.⋆ h) Eq.refl (Eq.pathToEq (sym (C.⋆Assoc f g h)))
        fᴰ gᴰ hᴰ
      ◁ Cᴰ.⋆ᴰ-coh f (g C.⋆ h) ((f C.⋆ g) C.⋆ h) (f C.⋆ (g C.⋆ h))
          (Eq.pathToEq (sym (C.⋆Assoc f g h))) Eq.refl (C.⋆Assoc f g h)
          fᴰ (Cᴰ.⋆ᴰ g h (g C.⋆ h) Eq.refl gᴰ hᴰ))
  toCategoryᴰ .isSetHomᴰ = Cᴰ.isSetHomᴰ

-- ------------------------------------------------------------------
-- FIBREWISE PRODUCT, direct.
module _ {C : Category Cob CHom-ℓ}
  {obᴰ obᴰ' : Cob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
  {Hom-ℓᴰ' : ∀ x y (xᴰ : obᴰ' x) (yᴰ : obᴰ' y) → Level}
  (Cᴰ : Categoryᶠᴰ C obᴰ Hom-ℓᴰ) (Dᴰ : Categoryᶠᴰ C obᴰ' Hom-ℓᴰ')
  where
  private
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module Dᴰ = Categoryᶠᴰ Dᴰ

  _×ᶠᴰ_ : Categoryᶠᴰ C (λ x → Σω[ _ ∈ obᴰ x ] obᴰ' x)
    (λ x y xx yy → ℓ-max (Hom-ℓᴰ x y (xx .fst) (yy .fst))
                         (Hom-ℓᴰ' x y (xx .snd) (yy .snd)))
  _×ᶠᴰ_ .Hom[_][_,_] f xx yy =
    Cᴰ.Hom[ f ][ xx .fst , yy .fst ] × Dᴰ.Hom[ f ][ xx .snd , yy .snd ]
  _×ᶠᴰ_ .idᴰ i ei = Cᴰ.idᴰ i ei , Dᴰ.idᴰ i ei
  _×ᶠᴰ_ .⋆ᴰ f g h e (fᴰ , fᴰ') (gᴰ , gᴰ') =
    Cᴰ.⋆ᴰ f g h e fᴰ gᴰ , Dᴰ.⋆ᴰ f g h e fᴰ' gᴰ'
  _×ᶠᴰ_ .⋆IdLᴰ i ei f e (fᴰ , fᴰ') =
    ΣPathP (Cᴰ.⋆IdLᴰ i ei f e fᴰ , Dᴰ.⋆IdLᴰ i ei f e fᴰ')
  _×ᶠᴰ_ .⋆IdRᴰ f i ei e (fᴰ , fᴰ') =
    ΣPathP (Cᴰ.⋆IdRᴰ f i ei e fᴰ , Dᴰ.⋆IdRᴰ f i ei e fᴰ')
  _×ᶠᴰ_ .⋆Assocᴰ f g h fg efg gh egh k e₁ e₂
    (fᴰ , fᴰ') (gᴰ , gᴰ') (hᴰ , hᴰ') =
    ΣPathP (Cᴰ.⋆Assocᴰ f g h fg efg gh egh k e₁ e₂ fᴰ gᴰ hᴰ ,
            Dᴰ.⋆Assocᴰ f g h fg efg gh egh k e₁ e₂ fᴰ' gᴰ' hᴰ')
  _×ᶠᴰ_ .idᴰ-coh i i' ei ei' p =
    ΣPathP (Cᴰ.idᴰ-coh i i' ei ei' p , Dᴰ.idᴰ-coh i i' ei ei' p)
  _×ᶠᴰ_ .⋆ᴰ-coh f g h h' e e' p (fᴰ , fᴰ') (gᴰ , gᴰ') =
    ΣPathP (Cᴰ.⋆ᴰ-coh f g h h' e e' p fᴰ gᴰ ,
            Dᴰ.⋆ᴰ-coh f g h h' e e' p fᴰ' gᴰ')
  _×ᶠᴰ_ .isSetHomᴰ = isSet× Cᴰ.isSetHomᴰ Dᴰ.isSetHomᴰ

-- ------------------------------------------------------------------
-- SMALL FIBRES, forded.  Same synonyms as
-- Displayed.Category.Small / .SmallDisplayedFibers, with `Categoryᴰ`
-- replaced by `Categoryᶠᴰ`.
SmallFibersCategoryᶠᴰ : (C : Category Cob CHom-ℓ)
  (obᴰ-ℓ : Cob → Level) (obᴰ : ∀ x → Type (obᴰ-ℓ x))
  (Homᴰ-ℓ : Cob → Cob → Level) → Typeω
SmallFibersCategoryᶠᴰ C obᴰ-ℓ obᴰ Homᴰ-ℓ =
  Categoryᶠᴰ C (λ x → Liftω (obᴰ x)) (λ x y _ _ → Homᴰ-ℓ x y)

GloballySmallCategoryᶠᴰ : (C : Category Cob CHom-ℓ)
  (obᴰ : Cob → Typeω) (ℓᴰ' : Level) → Typeω
GloballySmallCategoryᶠᴰ C obᴰ ℓᴰ' = Categoryᶠᴰ C obᴰ (λ _ _ _ _ → ℓᴰ')

module _ {C : Category Cob CHom-ℓ}
  {obᴰ : Cob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
  {obᴰ' : Cob → Typeω}
  {Hom-ℓᴰ' : ∀ x y (xᴰ : obᴰ' x) (yᴰ : obᴰ' y) → Level}
  (Cᴰ : Categoryᶠᴰ C obᴰ Hom-ℓᴰ) (Dᴰ : Categoryᶠᴰ C obᴰ' Hom-ℓᴰ')
  where

  SmallFibersᶠᴰCategoryᶠᴰ :
    (obᴰᴰ-ℓ : (c : Cob) → obᴰ c → Level)
    (obᴰᴰ : ∀ (x : Ob (∫ᶠ (Cᴰ ×ᶠᴰ Dᴰ)))
      → Type (obᴰᴰ-ℓ (x .fst) (x .snd .fst)))
    (Hom-ℓᴰᴰ : (c c' : Cob) (cᴰ : obᴰ c) (cᴰ' : obᴰ c') → Level)
    → Typeω
  SmallFibersᶠᴰCategoryᶠᴰ obᴰᴰ-ℓ obᴰᴰ Hom-ℓᴰᴰ =
    SmallFibersCategoryᶠᴰ (∫ᶠ (Cᴰ ×ᶠᴰ Dᴰ)) _ obᴰᴰ
      (λ x y → Hom-ℓᴰᴰ (x .fst) (y .fst) (x .snd .fst) (y .snd .fst))

-- ------------------------------------------------------------------
-- THE DISPLAYED FIBRE, over the fibre of `Dᴰ` at `c` with the `Cᴰ`
-- coordinate pinned at `cᴰ`.  Two witnesses about the BASE are
-- needed and both are structural: `C-⋆` says `C.id` is idempotent,
-- `Cᴰ-⋆` says `Cᴰ.idᴰ` is.  Neither is about the functor, and no
-- `F-seq'` is posited -- it is derived from them.
module _ {C : Category Cob CHom-ℓ}
  {obᴰ : Cob → Typeω}
  {Hom-ℓᴰ : ∀ x y (xᴰ : obᴰ x) (yᴰ : obᴰ y) → Level}
  {obᴰ' : Cob → Typeω}
  {Hom-ℓᴰ' : ∀ x y (xᴰ : obᴰ' x) (yᴰ : obᴰ' y) → Level}
  (Cᴰ : Categoryᶠᴰ C obᴰ Hom-ℓᴰ) (Dᴰ : Categoryᶠᴰ C obᴰ' Hom-ℓᴰ')
  (c : Cob) (cᴰ : obᴰ c)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᶠᴰ Cᴰ
    module Dᴰ = Categoryᶠᴰ Dᴰ

  module _ (C-⋆ : C.Id⋆Eq)
    (Cᴰ-⋆ : Cᴰ.⋆ᴰ C.id C.id C.id C-⋆ (Cᴰ.idᴰ C.id Eq.refl)
              (Cᴰ.idᴰ C.id Eq.refl) Eq.≡ Cᴰ.idᴰ C.id Eq.refl)
    where
    private
      Prod = Cᴰ ×ᶠᴰ Dᴰ
      module Prod = Categoryᶠᴰ Prod

      ι-seqᴰ : ∀ {dᴰ eᴰ fᴰ : obᴰ' c}
        (u : C.Hom[ c , c ]) (q : C.id C.⋆ C.id Eq.≡ u)
        (uᴰ : Cᴰ.Hom[ u ][ cᴰ , cᴰ ])
        (qᴰ : Cᴰ.⋆ᴰ C.id C.id u q (Cᴰ.idᴰ C.id Eq.refl)
                (Cᴰ.idᴰ C.id Eq.refl) Eq.≡ uᴰ)
        (f : Dᴰ.Hom[ C.id ][ dᴰ , eᴰ ]) (g : Dᴰ.Hom[ C.id ][ eᴰ , fᴰ ])
        (h : Dᴰ.Hom[ u ][ dᴰ , fᴰ ])
        → Dᴰ.⋆ᴰ C.id C.id u q f g Eq.≡ h
        → Eq._≡_
            {A = Σ[ k ∈ C.Hom[ c , c ] ]
                   Prod.Hom[ k ][ (cᴰ , dᴰ) , (cᴰ , fᴰ) ]}
            (C.id C.⋆ C.id ,
               Prod.⋆ᴰ C.id C.id (C.id C.⋆ C.id) Eq.refl
                 (Cᴰ.idᴰ C.id Eq.refl , f) (Cᴰ.idᴰ C.id Eq.refl , g))
            (u , (uᴰ , h))
      ι-seqᴰ u Eq.refl uᴰ Eq.refl f g h Eq.refl = Eq.refl

    ιᶠᴰ : StrictFunctor (fibᶠ Dᴰ C-⋆ c) (∫ᶠ Prod)
    ιᶠᴰ .F-ob dᴰ = c , (cᴰ , dᴰ)
    ιᶠᴰ .F-hom fᴰ = C.id , (Cᴰ.idᴰ C.id Eq.refl , fᴰ)
    ιᶠᴰ .F-id f e =
      Eq.ap (λ u → C.id , (Cᴰ.idᴰ C.id Eq.refl , u)) e
    ιᶠᴰ .F-seq f g h e =
      ι-seqᴰ C.id C-⋆ (Cᴰ.idᴰ C.id Eq.refl) Cᴰ-⋆ f g h e

    module _
      {obᴰᴰ : Ob (∫ᶠ Prod) → Typeω}
      {Hom-ℓᴰᴰ : ∀ x y (xᴰ : obᴰᴰ x) (yᴰ : obᴰᴰ y) → Level}
      (Cᴰᴰ : Categoryᶠᴰ (∫ᶠ Prod) obᴰᴰ Hom-ℓᴰᴰ)
      where

      fibᶠᴰ : Categoryᶠᴰ (fibᶠ Dᴰ C-⋆ c) (λ dᴰ → obᴰᴰ (c , (cᴰ , dᴰ))) _
      fibᶠᴰ = reindexS ιᶠᴰ Cᴰᴰ

      -- STRICTNESS.  Inhabited by the identity, so both sides are
      -- definitionally equal.  These are `reindexS-Id` and
      -- `reindexS-comp` (Displayed.Category.Forded) instantiated at
      -- the fibre, and they hold because `reindexS` writes no `reind`
      -- into any field: the stock `reindex` writes one at `idᴰ` and
      -- one at every `⋆ᴰ`, so each reindexing step there adds a
      -- transport.
      fibᶠᴰ-reindex-Id : Coe (reindexS SId fibᶠᴰ) fibᶠᴰ
      fibᶠᴰ-reindex-Id P x = x

      fibᶠᴰ-factors : {Eob : Typeω} {EHom-ℓ : Eob → Eob → Level}
        {E : Category Eob EHom-ℓ} (F : StrictFunctor E (fibᶠ Dᴰ C-⋆ c))
        → Coe (reindexS (ιᶠᴰ S∘ F) Cᴰᴰ) (reindexS F fibᶠᴰ)
      fibᶠᴰ-factors F P x = x
