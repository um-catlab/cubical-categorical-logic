-- The walking parallel pair `V ⇉ E` as a non-thin direct category
module Cubical.Categories.Direct.Instances.ParallelPair where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum using (inl ; inr)
import Cubical.Data.Equality as Eq
open import Cubical.Data.Nat using (ℕ ; isSetℕ)

open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat using (ℕWFOrder)

data Ob : Type where
  V E : Ob

Hom : Ob → Ob → Type
Hom V V = Unit
Hom V E = Bool
Hom E E = Unit
Hom E V = ⊥

s t : Hom V E
s = false
t = true

idH : (x : Ob) → Hom x x
idH V = tt
idH E = tt

_⋆ₚ_ : {x y z : Ob} → Hom x y → Hom y z → Hom x z
_⋆ₚ_ {V} {V} {V} f g = tt
_⋆ₚ_ {V} {V} {E} f g = g
_⋆ₚ_ {V} {E} {E} f g = f
_⋆ₚ_ {V} {E} {V} f g = ⊥.rec g
_⋆ₚ_ {E} {E} {E} f g = tt
_⋆ₚ_ {E} {E} {V} f g = ⊥.rec g
_⋆ₚ_ {E} {V}     f g = ⊥.rec f

isSetHomₚ : {x y : Ob} → isSet (Hom x y)
isSetHomₚ {V} {V} = isSetUnit
isSetHomₚ {V} {E} = isSetBool
isSetHomₚ {E} {E} = isSetUnit
isSetHomₚ {E} {V} = isProp→isSet isProp⊥

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
ParallelPair .isSetHom  = isSetHomₚ

deg : Ob → ℕ
deg V = 0
deg E = 1

ParallelPairDirect : DirectStr {C = ParallelPair} ℕWFOrder
ParallelPairDirect = mkDirectStr {C = ParallelPair} ℕWFOrder deg non-dec
  where
    non-dec : {x y : Ob} → Hom x y → WFOrder._≤_ ℕWFOrder (deg x) (deg y)
    non-dec {V} {V} _ = inr Eq.refl
    non-dec {V} {E} _ = inl tt
    non-dec {E} {E} _ = inr Eq.refl
    non-dec {E} {V} f = ⊥.rec f
