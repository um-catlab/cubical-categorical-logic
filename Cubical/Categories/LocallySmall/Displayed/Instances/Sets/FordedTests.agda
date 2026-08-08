{-
  WHAT THE FORDED SETS TELESCOPE ACTUALLY CONTAINS.

  `∫ᶠ SETᴰᶠ` is claimed to be the category whose objects are the
  telescope

      (ℓ : Level) (ℓ' : Level) (A : hSet ℓ) (B : ⟨ A ⟩ → hSet ℓ')

  and whose morphisms are a function `⟨ A ⟩ → ⟨ A' ⟩` together with a
  fibrewise map over it.  Every test below is a concrete inhabitant, a
  `refl` at a computed type, or the identity at a `Coe`, so each one
  fails unless the computation is the expected one ON THE NOSE.

  Note on what can even be STATED: objects live in `Typeω`, where
  `Path` is unavailable, so object-level equations go through `Coe`.
  Hom-types are honest `Type ℓ`, so those are ordinary `≡`.
-}
module Cubical.Categories.LocallySmall.Displayed.Instances.Sets.FordedTests
  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Functor.Strict
open import Cubical.Categories.LocallySmall.Displayed.Category.Forded
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Forded

open Category
open StrictFunctor
open Σω
open Liftω

-- THE TELESCOPE CATEGORY
TELE : Category _ _
TELE = ∫ᶠ SETᴰᶠ

-- ------------------------------------------------------------------
-- 1.  OBJECTS ARE FOUR-COMPONENT TELESCOPES.
BoolSet : hSet ℓ-zero
BoolSet = Bool , isSetBool

NatSet : hSet ℓ-zero
NatSet = ℕ , isSetℕ

Fam : Bool → hSet ℓ-zero
Fam true  = Unit , isSetUnit
Fam false = ℕ , isSetℕ

Fam' : ℕ → hSet ℓ-zero
Fam' _ = Bool , isSetBool

-- built by hand, so the four-component shape is checked and not
-- inferred: ((ℓ , (ℓ' , A)) , B)
src tgt : Ob TELE
src = (liftω ℓ-zero , (liftω ℓ-zero , liftω BoolSet)) , liftω Fam
tgt = (liftω ℓ-zero , (liftω ℓ-zero , liftω NatSet)) , liftω Fam'

-- the components are where we say they are
levels : Ob TELE → Σω[ _ ∈ Liftω Level ] Liftω Level
levels ((l , (l' , _)) , _) = l , l'

-- ------------------------------------------------------------------
-- 2.  MORPHISMS ARE (a function on carriers, a fibrewise map over it).
--     Stated as `refl` between TYPES: fails unless TELE's hom computes
--     to exactly this Σ.  The two `Unit`s are the LEVEL homs, trivial
--     because LEVEL is indiscrete -- which is precisely why the ford
--     costs nothing at those layers.
hom-computes :
  TELE .Hom[_,_] src tgt
  ≡ (Σ[ f ∈ (Unit × (Unit × (Bool → ℕ))) ]
      ((b : Bool) → ⟨ Fam b ⟩ → ⟨ Fam' (f .snd .snd b) ⟩))
hom-computes = refl

toNat : Bool → ℕ
toNat true = 1
toNat false = 0

amor : TELE .Hom[_,_] src tgt
amor = (tt , (tt , toNat)) , λ { true _ → true ; false n → false }

-- ------------------------------------------------------------------
-- 3.  COMPOSITION WITH THE IDENTITY COMPUTES, on the nose.
⋆IdL-computes : (TELE ._⋆_ {src} {src} {tgt} (TELE .id {src}) amor) ≡ amor
⋆IdL-computes = refl

⋆IdR-computes : (TELE ._⋆_ {src} {tgt} {tgt} amor (TELE .id {tgt})) ≡ amor
⋆IdR-computes = refl

-- ------------------------------------------------------------------
-- 4.  THE DISPLAY MAP FORGETS EXACTLY THE FAMILY.
π : StrictFunctor TELE _
π = Fstᶠ SETᴰᶠ

-- on objects (via Coe, since Ob is Typeω)
π-forgets-family :
  Coe (π .F-ob src) (liftω ℓ-zero , (liftω ℓ-zero , liftω BoolSet))
π-forgets-family P x = x

-- on morphisms it is literally the first projection
π-on-homs : π .F-hom {src} {tgt} amor ≡ (tt , (tt , toNat))
π-on-homs = refl

-- ------------------------------------------------------------------
-- 5.  THE STRICTNESS THAT MOTIVATED ALL THIS, at the families layer.
--     Inhabited by the identity, so both sides are definitionally
--     equal.  The stock `reindex` has neither property.
tele-reindex-Id : Coe (reindexS SId SETᴰᶠ) SETᴰᶠ
tele-reindex-Id P x = x

tele-reindex-comp : (F : StrictFunctor TELE _)
  → Coe (reindexS (SId S∘ F) SETᴰᶠ) (reindexS F (reindexS SId SETᴰᶠ))
tele-reindex-comp F P x = x

-- and the display maps compose strictly
π-assoc : (F : StrictFunctor TELE TELE)
  → Coe ((π S∘ F) S∘ F) (π S∘ (F S∘ F))
π-assoc F P x = x

-- ------------------------------------------------------------------
-- 5b.  THE LIFTED LAYER COMPUTES TOO, now that the ford is Eq-valued.
--
-- Under the earlier Path-valued ford this FAILED: `fromCategoryᴰ`'s
-- `idᴰ i ei` was `reind ei idᴰ`, a `subst`, and `subst B refl b` is
-- stuck for neutral `B`.  With the ford oriented forwards it can be
-- `Eq`, `fromCategoryᴰ` uses `Eq.transport`, and
-- `Eq.transport C Eq.refl b` REDUCES to `b`.  So lifting an existing
-- Categoryᴰ now buys strict REINDEXING (tests 5) AND an identity that
-- computes.
id-fibre : (TELE .id {src}) .snd ≡ (λ b p → p)
id-fibre = refl

-- ------------------------------------------------------------------
-- 6.  THE DIRECTLY-DEFINED LAYER HAS NO TRANSPORT AT ALL.
--     `SETᶠ` ignores its ford arguments outright, so unlike the lifted
--     `SETᴰᶠ` its identity computes to the identity function.  This is
--     the gap noted at the bottom of this file, closed for any layer
--     defined forded rather than lifted.
SETTOT' : Category _ _
SETTOT' = ∫ᶠ SETᶠ

BoolPt : Ob SETTOT'
BoolPt = liftω ℓ-zero , liftω BoolSet

id-computes : (SETTOT' .id {BoolPt}) .snd ≡ (λ x → x)
id-computes = refl

-- ------------------------------------------------------------------
-- 7.  ORDER-INDEPENDENT TELESCOPES, at Typeω.
--     Two formers over LEVEL: "add a set" and "add another level".
setExt levelExt : Ext LEVELᶜ
setExt   = ⌜ SETᶠ ⌝
levelExt = ⌜ weakenᶠ LEVELᶜ LEVELᶜ ⌝

-- building (set , level , set) either way gives the SAME former
tele-order :
  Coe₁ ((setExt ·ᶠ levelExt) ·ᶠ setExt) (setExt ·ᶠ (levelExt ·ᶠ setExt))
tele-order P x = x

-- and the unit is neutral at every position
tele-unit-mid : Coe₁ ((setExt ·ᶠ εE) ·ᶠ levelExt) (setExt ·ᶠ levelExt)
tele-unit-mid P x = x

-- the bridge recovers the total category on the nose
bridge-recovers : Coe (setExt .Ext.at LEVELᶜ SId) (∫ᶠ SETᶠ)
bridge-recovers P x = x
