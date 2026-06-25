-- The parallel pair `•⇉•` as a genuinely non-thin direct category.
module Cubical.Categories.Direct.Instances.ParallelPair where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; isSetℕ)

open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.StrictDownset using (löbStr)
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)

data Ob : Type where
  V E : Ob

Hom : Ob → Ob → Type
Hom V V = Unit
Hom V E = Bool        -- the two parallel maps:  false = source, true = target
Hom E E = Unit
Hom E V = ⊥

idH : (x : Ob) → Hom x x
idH V = tt
idH E = tt

-- composition is forced by the identity laws (there are no composable pairs
-- of non-identities), so it just shuffles identities / eliminates the empty
-- `Hom E V`.
_⋆ₚ_ : {x y z : Ob} → Hom x y → Hom y z → Hom x z
_⋆ₚ_ {V} {V} {V} f g = tt
_⋆ₚ_ {V} {V} {E} f g = g
_⋆ₚ_ {V} {E} {E} f g = f
_⋆ₚ_ {V} {E} {V} f g = ⊥.rec g
_⋆ₚ_ {E} {E} {E} f g = tt
_⋆ₚ_ {E} {E} {V} f g = ⊥.rec g
_⋆ₚ_ {E} {V}     f g = ⊥.rec f

isSetHom' : {x y : Ob} → isSet (Hom x y)
isSetHom' {V} {V} = isSetUnit
isSetHom' {V} {E} = isSetBool
isSetHom' {E} {E} = isSetUnit
isSetHom' {E} {V} = isProp→isSet isProp⊥

open Category

ParallelPair : Category ℓ-zero ℓ-zero
ParallelPair .ob        = Ob
ParallelPair .Hom[_,_]  = Hom
ParallelPair .id {x}    = idH x
ParallelPair ._⋆_       = _⋆ₚ_
ParallelPair .⋆IdL {V} {V} f = refl
ParallelPair .⋆IdL {V} {E} f = refl
ParallelPair .⋆IdL {E} {E} f = refl
ParallelPair .⋆IdL {E} {V} f = ⊥.rec f
ParallelPair .⋆IdR {V} {V} f = refl
ParallelPair .⋆IdR {V} {E} f = refl
ParallelPair .⋆IdR {E} {E} f = refl
ParallelPair .⋆IdR {E} {V} f = ⊥.rec f
ParallelPair .⋆Assoc {V} {V} {V} {V} f g h = refl
ParallelPair .⋆Assoc {V} {V} {V} {E} f g h = refl
ParallelPair .⋆Assoc {V} {V} {E} {E} f g h = refl
ParallelPair .⋆Assoc {V} {E} {E} {E} f g h = refl
ParallelPair .⋆Assoc {E} {E} {E} {E} f g h = refl
ParallelPair .⋆Assoc {E} {V}         f g h = ⊥.rec f
ParallelPair .⋆Assoc {V} {E} {V}     f g h = ⊥.rec g
ParallelPair .⋆Assoc {E} {E} {V}     f g h = ⊥.rec g
ParallelPair .⋆Assoc {V} {V} {E} {V} f g h = ⊥.rec h
ParallelPair .⋆Assoc {V} {E} {E} {V} f g h = ⊥.rec h
ParallelPair .⋆Assoc {E} {E} {E} {V} f g h = ⊥.rec h
ParallelPair .isSetHom  = isSetHom'

-- the degree functor: V ↦ 0, E ↦ 1.  Non-identity maps (V → E) strictly
-- raise degree, so ParallelPair is direct.
deg : Ob → ℕ
deg V = 0
deg E = 1

ParallelPairDirect : DirectStr {C = ParallelPair} ℕWFOrder
ParallelPairDirect = mkDirectStr {C = ParallelPair} ℕWFOrder deg non-dec
  where
    non-dec : {x y : Ob} → Hom x y → WFOrder._≤_ ℕWFOrder (deg x) (deg y)
    non-dec {V} {V} _ = inr refl
    non-dec {V} {E} _ = inl _          -- 0 < 1
    non-dec {E} {E} _ = inr refl
    non-dec {E} {V} f = ⊥.rec f

private
  A : Ob → hSet ℓ-zero
  A V = ℕ , isSetℕ
  A E = ℕ , isSetℕ

label : ∀ x → ⟨ A x ⟩
label = löbStr ParallelPairDirect {ℓF = ℓ-zero} A λ where
  V _   → 5                                  -- vertex label (minimal: no inputs)
  E rec → rec V false _ + rec V true _       -- edge label = source-label + target-label

-- _ : label V ≡ 5
-- _ = refl

-- _ : label E ≡ 10
-- _ = refl
