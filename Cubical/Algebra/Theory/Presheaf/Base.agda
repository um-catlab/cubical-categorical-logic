{-# OPTIONS --lossy-unification #-}
-- Presheaf-valued models of an algebraic theory, displayed over
-- PRESHEAF (the strict-hom presheaf category)
module Cubical.Algebra.Theory.Presheaf.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base

open import Cubical.Data.Sigma

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category using (MOD ; noEqns)

private
  variable
    ℓ ℓ' ℓ'' ℓv ℓX ℓY ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} {σ : AlgTheorySig ℓ ℓ'}
  (σeq : AlgTheoryEqns σ ℓ'' ℓv) where

  -- A model of σeq valued in presheaves over C: a fibrewise algebra
  -- whose restriction maps are algebra homomorphisms.  Note `Homo` is
  -- already forded, so this record carries no non-forded equations.
  record PshAlg (P : Presheaf C ℓX)
    : Type (ℓ-max (ℓ-max ℓC ℓC')
             (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max (ℓ-max ℓ'' ℓv) ℓX))) where
    open PresheafNotation P
    field
      alg : ∀ (c : Category.ob C) → Alg σeq p[ c ]
      restr : ∀ {c c'} (f : C [ c , c' ])
        → Homo σeq (_⋆_ f) (alg c') (alg c)

  open PshAlg
  open PshHomStrict

  -- A homomorphism of presheaf models over a strict presheaf morphism
  -- is a *bare family* of algebra homomorphisms.
  PshAlgHomo : {P : Presheaf C ℓX} {Q : Presheaf C ℓY}
    (α : PshHomStrict P Q) (B : PshAlg P) (D : PshAlg Q) → Type _
  PshAlgHomo {P = P} {Q = Q} α B D =
    ∀ (c : Category.ob C) → Homo σeq (α .N-ob c) (B .alg c) (D .alg c)

  PMODᴰ : (ℓX : Level) → Categoryᴰ (PRESHEAF C ℓX) _ _
  PMODᴰ ℓX .Categoryᴰ.ob[_] P = PshAlg P
  PMODᴰ ℓX .Categoryᴰ.Hom[_][_,_] α B D = PshAlgHomo α B D
  PMODᴰ ℓX .Categoryᴰ.idᴰ c = idHomo σeq
  PMODᴰ ℓX .Categoryᴰ._⋆ᴰ_ ϕ ψ c = _⋆Homo_ σeq (ϕ c) (ψ c)
  PMODᴰ ℓX .Categoryᴰ.⋆IdLᴰ fᴰ = refl
  PMODᴰ ℓX .Categoryᴰ.⋆IdRᴰ fᴰ = refl
  PMODᴰ ℓX .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ = refl
  PMODᴰ ℓX .Categoryᴰ.isSetHomᴰ {y = Q} =
    isSetΠ λ c → isProp→isSet (isPropHomo σeq (str (Q ⟅ c ⟆)))

  PMOD : (ℓX : Level) → Category _ _
  PMOD ℓX = ∫C (PMODᴰ ℓX)

  -- a homomorphism of presheaf models
  PModHom : (ℓX : Level) (M N : Category.ob (PMOD ℓX)) → Type _
  PModHom ℓX M N = PMOD ℓX [ M , N ]

  ForgetPsh : Functor (PMOD ℓX) (PRESHEAF C ℓX)
  ForgetPsh = Fst

  -- Pointwise description: a presheaf model is exactly a family of
  -- algebras together with the (forded) statement that restriction is
  -- a homomorphism.
  module _ (P : Presheaf C ℓX) where
    private module P = PresheafNotation P

    PshAlgΣ : Type _
    PshAlgΣ =
      Σ[ A ∈ (∀ (c : Category.ob C) → Alg σeq P.p[ c ]) ]
        (∀ {c c'} (f : C [ c , c' ]) → Homo σeq (P._⋆_ f) (A c') (A c))

    PshAlgIsoΣ : Iso (PshAlg P) PshAlgΣ
    PshAlgIsoΣ .Iso.fun B = B .alg , B .restr
    PshAlgIsoΣ .Iso.inv B .alg = B .fst
    PshAlgIsoΣ .Iso.inv B .restr = B .snd
    PshAlgIsoΣ .Iso.sec _ = refl
    PshAlgIsoΣ .Iso.ret _ = refl

  -- Evaluation at an object: a strict functor to the SET-valued models
  module _ (c : Category.ob C) where
    open Functor
    Ev : Functor (PMOD ℓX) (MOD σeq ℓX)
    Ev .F-ob M = (M .fst ⟅ c ⟆) , M .snd .alg c
    Ev .F-hom α = α .fst .N-ob c , α .snd c
    Ev .F-id = refl
    Ev .F-seq _ _ = refl

module _ {C : Category ℓC ℓC'} (σ : AlgTheorySig ℓ ℓ') where
  PALGᴰ : (ℓX : Level) → Categoryᴰ (PRESHEAF C ℓX) _ _
  PALGᴰ = PMODᴰ (noEqns σ)

  PALG : (ℓX : Level) → Category _ _
  PALG = PMOD {C = C} (noEqns σ)
