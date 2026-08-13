-- A sieve on `c` is a subobject of the representable presheaf `よc`.
--
-- This instantiates the general displayed-category notion of subobject
-- (`Cubical.Categories.Subobject.Base`) at `(PRESHEAF C , よc)`, where
-- PRESHEAF has *strict* presheaf morphisms (`PshHomStrict`) as homs — the
-- same category used for the presheaf/family monadicity.  A sieve is thus a
-- sub-presheaf `S` of `よc` together with the proof that the inclusion
-- `S ↪ よc` is monic.
module Cubical.Categories.Presheaf.Sieve where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Subobject.Base

private
  variable
    ℓ ℓ' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  -- a sieve on c = a subobject of the representable よc in PRESHEAF
  Sieve : ob → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  Sieve c = Subobject (PRESHEAF C ℓ') (yo c)

module _ {C : Category ℓ ℓ'} where
  open Category C
  open Functor
  open PshHomStrict

  module _ {c : ob} where
    -- the underlying sub-presheaf
    sievePsh : Sieve C c → Presheaf C ℓ'
    sievePsh = sub-dom (PRESHEAF C ℓ') (yo c)

    -- the inclusion S ↪ よc (a strict presheaf morphism)
    sieveIncl : (S : Sieve C c) → PshHomStrict (sievePsh S) (yo c)
    sieveIncl = sub-incl (PRESHEAF C ℓ') (yo c)

    -- "S contains f": f : y → c lies in the image of the inclusion
    _∋_ : (S : Sieve C c) {y : ob} (f : C [ y , c ]) → Type ℓ'
    _∋_ S {y} f = Σ[ t ∈ ⟨ sievePsh S .F-ob y ⟩ ] (sieveIncl S .N-ob y t ≡ f)

    -- sieves are closed under precomposition
    sieve-precomp : (S : Sieve C c) {y z : ob} {f : C [ y , c ]} (g : C [ z , y ])
      → S ∋ f → S ∋ (g ⋆ f)
    sieve-precomp S {y} {z} {f} g (t , eq) =
      sievePsh S .F-hom g t ,
      sym (sieveIncl S .N-hom z y g t (sievePsh S .F-hom g t) refl)
      ∙ cong (yo {C = C} c .F-hom g) eq

    -- proper: does not contain the identity
    isProperSieve : Sieve C c → Type ℓ'
    isProperSieve S = ¬ (S ∋ id)

    -- refinement order on sieves
    _⊆_ : Sieve C c → Sieve C c → Type (ℓ-max ℓ ℓ')
    S ⊆ T = ∀ {y} (f : C [ y , c ]) → S ∋ f → T ∋ f
