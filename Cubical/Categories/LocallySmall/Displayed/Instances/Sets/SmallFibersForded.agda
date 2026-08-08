{-# OPTIONS --lossy-unification #-}
{-
  THE SMALL-FIBRE BOOKKEEPING FOR SETS.

  Sets.Base builds the fibre of SET at a level, and of SETᴰ over it,
  as

    SETAtEq  ℓ    = smallcat  _ (fibEq SET Eq.refl (liftω ℓ))
    SETᴰAtEq ℓ ℓ' = smallcatᴰ _
      (fibᴰEq LEVEL (weaken LEVEL LEVEL) SET SETᴰ (liftω ℓ) (liftω ℓ')
        Eq.refl (λ _ _ → Eq.refl))

  Here the corresponding two constructions are built from `fibᶠ` and
  `fibᶠᴰ`.  ACCOUNTING, honestly:

    * the `Id⋆Eq` witness does NOT go away -- `fibᶠ` takes `Eq.refl`
      exactly as `fibEq` does, because composing two fibre morphisms
      really does land over `C.id ⋆ C.id`;
    * the `F-seq'` obligation DOES -- `fibᴰEq`'s second argument, six
      lines of `Eq`-valued statement about the composite functor
      `fibᴰF ∘F fibEq→fib`, is derived here from `C-⋆` inside `ιᶠᴰ`;
    * the `fibEq→fib` correction functor goes away, since there is one
      fibre construction rather than `fib` and `fibEq`;
    * `_×ᴰ_`'s internal `reindexEq Δ ... Eq.refl (λ _ _ → Eq.refl)`
      goes away, `_×ᶠᴰ_` being direct;
    * what `ιᶠᴰ` does ask for instead is `Cᴰ-⋆`, that `Cᴰ.idᴰ` is
      idempotent -- one `Eq.refl` here, and a statement about the BASE
      rather than about a functor.

  In exchange, reindexing is strictly functorial (`SETᴰAtᶠ-factors`),
  and `idᴰ`/`⋆ᴰ` still COMPUTE (`fibᴰ-id-computes`,
  `fibᴰ-⋆-computes`), matching `SETᴰAtEq`.
-}
module Cubical.Categories.LocallySmall.Displayed.Instances.Sets.SmallFibersForded
  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Strict
open import Cubical.Categories.LocallySmall.Instances.Level

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Forded
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import
  Cubical.Categories.LocallySmall.Displayed.Category.SmallDisplayedFibers.Forded
open import Cubical.Categories.LocallySmall.Displayed.Instances.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.Instances.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base
  using (SET; SETᴰ)
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Forded
  using (LEVELᶜ; SETᶠ; SETᴰᶠ)

open Category
open Categoryᴰ using (∫C)
open StrictFunctor
open Σω
open Liftω

-- The second level, and the pair (ℓ , ℓ' , a set at ℓ), forded.
LEVELᶠ : Categoryᶠᴰ LEVELᶜ (λ _ → Liftω Level) _
LEVELᶠ = weakenᶠ LEVELᶜ LEVELᶜ

SETPAIRᶠ : Categoryᶠᴰ LEVELᶜ _ _
SETPAIRᶠ = LEVELᶠ ×ᶠᴰ SETᶠ

SETPAIRTOT : Category _ _
SETPAIRTOT = ∫ᶠ SETPAIRᶠ

-- ------------------------------------------------------------------
-- THE FORDED TELESCOPE IS THE STOCK ONE, ON THE NOSE.  `SETᴰ` is
-- displayed over `∫C (weaken LEVEL LEVEL ×ᴰ SET)`, where `_×ᴰ_` is
-- `reindexEq Δ (Cᴰ ×Cᴰ Dᴰ) Eq.refl (λ _ _ → Eq.refl)`.  The forded
-- `_×ᶠᴰ_` is direct.  That the identity functor is strict in BOTH
-- directions says the two agree definitionally on objects, homs,
-- identities and composites.
cmp : StrictFunctor SETPAIRTOT (∫C (weaken LEVEL LEVEL ×ᴰ SET))
cmp .F-ob x = x
cmp .F-hom f = f
cmp .F-id f e = e
cmp .F-seq f g h e = e

cmp⁻ : StrictFunctor (∫C (weaken LEVEL LEVEL ×ᴰ SET)) SETPAIRTOT
cmp⁻ .F-ob x = x
cmp⁻ .F-hom f = f
cmp⁻ .F-id f e = e
cmp⁻ .F-seq f g h e = e

-- ------------------------------------------------------------------
-- THE FIBRE AT A LEVEL.  Compare Sets.Base:
--
--     SETAt   ℓ = smallcat _ SET.v[ liftω ℓ ]
--     SETAtEq ℓ = smallcat _ (fibEq SET Eq.refl (liftω ℓ))
--
-- `v[_]` is `fib`, i.e. `reindex (elimUNIT c)`, whose identity and
-- composition are `reind`s -- transports -- so `SETAtEq` exists only
-- to replace them by `Eq.transport`s along `Eq.refl`, which compute.
-- `fibᶠ` needs neither: the base hom of a fibre morphism is PINNED to
-- `C.id` and the witness `C.id ⋆ C.id ≡ C.id` is passed as the ford
-- argument of `⋆ᴰ`, never as a transport.  No `Eq.refl`.
SETAtᶠ : (ℓ : Level) → SmallCategory (ℓ-suc ℓ) ℓ
SETAtᶠ ℓ = smallcat (hSet ℓ) (fibᶠ SETᶠ Eq.refl (liftω ℓ))

-- ------------------------------------------------------------------
-- THE DISPLAYED FIBRE.  Compare Sets.Base:
--
--     SETᴰAtEq ℓ ℓ' = smallcatᴰ _
--       (fibᴰEq LEVEL (weaken LEVEL LEVEL) SET SETᴰ (liftω ℓ) (liftω ℓ')
--         Eq.refl (λ _ _ → Eq.refl))
--
-- The two `Eq.refl`s are an `Id⋆Eq` for `LEVEL` and an `Eq`-valued
-- `F-seq'` for the composite functor `fibᴰF ∘F fibEq→fib`.  Below
-- there are none: `ιᶠᴰ` is a strict functor whose ford is discharged
-- generically, `cmp` moves to the base `SETᴰ` is actually displayed
-- over, and `reindexS` is transport-free.
SETᴰAtᶠ : (ℓ ℓ' : Level)
  → Categoryᶠᴰ (fibᶠ SETᶠ Eq.refl (liftω ℓ))
      (λ (liftω A) → Liftω (⟨ A ⟩ → hSet ℓ')) _
SETᴰAtᶠ ℓ ℓ' = reindexS
  (cmp S∘ ιᶠᴰ LEVELᶠ SETᶠ (liftω ℓ) (liftω ℓ') Eq.refl Eq.refl) SETᴰᶠ

-- and it packages as a `SmallCategoryᴰ` over `SETAtᶠ`, exactly as
-- `SETᴰAtEq ℓ ℓ' : SmallCategoryᴰ (SETAtEq ℓ) _ _` does.
SETᴰAtᶠSmall : (ℓ ℓ' : Level)
  → SmallCategoryᴰ (SETAtᶠ ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
SETᴰAtᶠSmall ℓ ℓ' = smallcatᴰ _ (toCategoryᴰ (SETᴰAtᶠ ℓ ℓ'))

-- ------------------------------------------------------------------
-- TESTS.  Each is `refl` at a computed type or the identity at a
-- `Coe`, so each fails unless the computation is on the nose.
open Categoryᶠᴰ

module _ {ℓ : Level} (A B D : hSet ℓ) where
  private
    S = fibᶠ SETᶠ Eq.refl (liftω ℓ)

  fib-hom-computes : S .Hom[_,_] (liftω A) (liftω B) ≡ (⟨ A ⟩ → ⟨ B ⟩)
  fib-hom-computes = refl

  fib-id-computes : S .id {liftω A} ≡ (λ x → x)
  fib-id-computes = refl

  fib-⋆-computes : (f : ⟨ A ⟩ → ⟨ B ⟩) (g : ⟨ B ⟩ → ⟨ D ⟩)
    → S ._⋆_ {liftω A} {liftω B} {liftω D} f g ≡ (λ x → g (f x))
  fib-⋆-computes f g = refl

module _ {ℓ ℓ' : Level} (A B : hSet ℓ)
  (Aᴰ : ⟨ A ⟩ → hSet ℓ') (Bᴰ : ⟨ B ⟩ → hSet ℓ') where

  fibᴰ-hom-computes : (f : ⟨ A ⟩ → ⟨ B ⟩)
    → SETᴰAtᶠ ℓ ℓ' .Hom[_][_,_] {x = liftω A} {y = liftω B}
        f (liftω Aᴰ) (liftω Bᴰ)
      ≡ (∀ (a : ⟨ A ⟩) → ⟨ Aᴰ a ⟩ → ⟨ Bᴰ (f a) ⟩)
  fibᴰ-hom-computes f = refl

-- The two-step fibre extraction IS the one-step one, on the nose:
-- `reindexS` writes no `reind` into any field, so composing strict
-- functors and composing reindexings agree definitionally.
SETᴰAtᶠ-factors : ∀ ℓ ℓ'
  → Coe (SETᴰAtᶠ ℓ ℓ')
      (reindexS (ιᶠᴰ LEVELᶠ SETᶠ (liftω ℓ) (liftω ℓ') Eq.refl Eq.refl)
        (reindexS cmp SETᴰᶠ))
SETᴰAtᶠ-factors ℓ ℓ' P x = x

-- ------------------------------------------------------------------
-- WHAT NOW HOLDS.  The displayed fibre's `idᴰ` and `⋆ᴰ` COMPUTE, on
-- the nose, matching `SETᴰAtEq`.  This is what the `Eq`-valued,
-- forward-oriented ford buys and a Path-valued ford cannot: the
-- witnesses reaching `SETᴰᶠ = fromCategoryᴰ SETᴰ` here are `Eq.refl`,
-- and `Eq.transport C Eq.refl b` REDUCES to `b`, whereas
-- `subst B refl b` is stuck for neutral `B` -- and `λ b → ⟨ Bᴰ b ⟩`
-- is neutral for a variable family `Bᴰ`.
module _ {ℓ ℓ' : Level} (A B D : hSet ℓ)
  (Aᴰ : ⟨ A ⟩ → hSet ℓ') (Bᴰ : ⟨ B ⟩ → hSet ℓ') (Dᴰ : ⟨ D ⟩ → hSet ℓ')
  where

  fibᴰ-id-computes :
    SETᴰAtᶠ ℓ ℓ' .idᴰ {xᴰ = liftω Aᴰ} (λ x → x) Eq.refl ≡ (λ a z → z)
  fibᴰ-id-computes = refl

  fibᴰ-⋆-computes : (f : ⟨ A ⟩ → ⟨ B ⟩) (g : ⟨ B ⟩ → ⟨ D ⟩)
    (fᴰ : ∀ a → ⟨ Aᴰ a ⟩ → ⟨ Bᴰ (f a) ⟩)
    (gᴰ : ∀ b → ⟨ Bᴰ b ⟩ → ⟨ Dᴰ (g b) ⟩)
    → SETᴰAtᶠ ℓ ℓ' .⋆ᴰ {xᴰ = liftω Aᴰ} {yᴰ = liftω Bᴰ} {zᴰ = liftω Dᴰ}
        f g (λ x → g (f x)) Eq.refl fᴰ gᴰ
      ≡ (λ a aᴰ → gᴰ (f a) (fᴰ a aᴰ))
  fibᴰ-⋆-computes f g fᴰ gᴰ = refl
