{-# OPTIONS --lossy-unification #-}
-- THE TOPOS OF TREES AS `PRESHEAF ℕCat`, WITH OUR LATER/LÖB — the
-- semantic model for the direct rebuild of the guarded canonicity, with
-- NO ωSet.  `ℕDirect` is the topos-of-trees base, so `▷ ℕDirect` /
-- `nextNT ℕDirect` are the later and its unit, and the guarded fixed
-- point is our `löb` (with `löb-fix` supplying the fixpoint equation).
module Cubical.Categories.Instances.PshℕGuarded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.FixedPoint
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder ; ℕCat ; ℕDirect)
open import Cubical.Categories.Direct.StrictDownset using (▷ ; nextNT ; löb ; löb-fix)

open Functor

private
  variable
    ℓ : Level

-- the later modality and its unit on the topos of trees `PRESHEAF ℕCat`
▷ℕ : Functor (PRESHEAF ℕCat ℓ-zero) (PRESHEAF ℕCat ℓ-zero)
▷ℕ = ▷ ℕDirect

nextℕ : ∀ (P : Presheaf ℕCat ℓ-zero) → PshHomStrict P (▷ℕ .F-ob P)
nextℕ P = NatTrans.N-ob (nextNT ℕDirect) P
  where open import Cubical.Categories.NaturalTransformation using (NatTrans)

-- THE GUARDED FIXED POINT, via our Löb: for f : ▷P → P, `löb` is a
-- global element of P and `löb-fix` says it is a fixed point of next ⋆ f.
guarded-fixed-points-Psh :
  {P : Presheaf ℕCat ℓ-zero}
  (f : PshHomStrict (▷ℕ .F-ob P) P)
  → fixed-point (PRESHEAF ℕCat ℓ-zero) UnitPsh (nextℕ P ⋆PshHomStrict f)
guarded-fixed-points-Psh {P = P} f .fst = löb ℕDirect P f
guarded-fixed-points-Psh {P = P} f .snd = sym (löb-fix ℕDirect P f)
