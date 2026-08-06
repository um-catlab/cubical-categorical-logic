{-# OPTIONS --lossy-unification #-}
-- The free/forgetful adjunction for a many-sorted theory, in the
-- `Closing` presentation.
module Cubical.Algebra.Theory.Sorted.Free.Adjunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.Profunctor.General

open import Cubical.Algebra.Theory.Sorted
  using (SortedSig; SortedEqns; FAM; MOD)
open import Cubical.Algebra.Theory.Sorted.Free.Closing
  using (FreeOb; gen; UPMod; InitialMOD)

private
  variable
    ℓS ℓ ℓ' ℓ'' : Level

open Functor

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' (ℓ-max (ℓ-max ℓS ℓ) (ℓ-max ℓ' ℓ''))) where

  private
    ℓX : Level
    ℓX = ℓ-max (ℓ-max ℓS ℓ) (ℓ-max ℓ' ℓ'')

    module F = Category (FAM S ℓX)
    module M = Category (MOD σeq ℓX)

  Forget : Functor (MOD σeq ℓX) (FAM S ℓX)
  Forget = Fst

  ΣFam : (X : S → hSet ℓX) → Type ℓX
  ΣFam X = Σ[ s ∈ S ] ⟨ X s ⟩

  FreeFamOb : (X : S → hSet ℓX) → Category.ob (MOD σeq ℓX)
  FreeFamOb X = FreeOb σeq (ΣFam X) fst

  private
    curryFam : (X : Category.ob (FAM S ℓX)) (N : Category.ob (MOD σeq ℓX))
      → Iso ((v : ΣFam X) → ⟨ N .fst (v .fst) ⟩)
            (FAM S ℓX [ X , Forget ⟅ N ⟆ ])
    curryFam X N .Iso.fun ρ s x = ρ (s , x)
    curryFam X N .Iso.inv g v = g (v .fst) (v .snd)
    curryFam X N .Iso.sec g = refl
    curryFam X N .Iso.ret ρ = refl

  adjIsoFam : (X : Category.ob (FAM S ℓX)) (N : Category.ob (MOD σeq ℓX))
    → Iso (MOD σeq ℓX [ FreeFamOb X , N ])
          (FAM S ℓX [ X , Forget ⟅ N ⟆ ])
  adjIsoFam X N = compIso (UPMod σeq (ΣFam X) fst N) (curryFam X N)

  genFam : (X : Category.ob (FAM S ℓX))
    → FAM S ℓX [ X , Forget ⟅ FreeFamOb X ⟆ ]
  genFam X s x = gen σeq (ΣFam X) fst (s , x)

  FreeUE : LeftAdjoint Forget
  FreeUE X .UniversalElement.vertex = FreeFamOb X
  FreeUE X .UniversalElement.element = genFam X
  FreeUE X .UniversalElement.universal N = isoToIsEquiv (adjIsoFam X N)

  private
    FreeOp : Functor ((FAM S ℓX) ^op) ((MOD σeq ℓX) ^op)
    FreeOp = FunctorComprehension (RightAdjointProf (Forget ^opF)) FreeUE

  Free : Functor (FAM S ℓX) (MOD σeq ℓX)
  Free = FreeOp ^opF⁻

  -- Readable names for the universal property at a fixed family.
  module FreeMod (X : Category.ob (FAM S ℓX)) where
    private
      module ue = UniversalElementNotation (FreeUE X)

    freeOb : Category.ob (MOD σeq ℓX)
    freeOb = ue.vertex

    unit : FAM S ℓX [ X , Forget ⟅ freeOb ⟆ ]
    unit = ue.element

    -- the unique extension of an assignment of generators
    rec : {N : Category.ob (MOD σeq ℓX)}
      → FAM S ℓX [ X , Forget ⟅ N ⟆ ] → MOD σeq ℓX [ freeOb , N ]
    rec = ue.intro

    recβ : {N : Category.ob (MOD σeq ℓX)}
      {ρ : FAM S ℓX [ X , Forget ⟅ N ⟆ ]}
      → F._⋆_ unit (Forget ⟪ rec {N = N} ρ ⟫) ≡ ρ
    recβ {N = N} {ρ = ρ} = ue.β {c = N} {p = ρ}

    recη : {N : Category.ob (MOD σeq ℓX)}
      {ψ : MOD σeq ℓX [ freeOb , N ]}
      → ψ ≡ rec (F._⋆_ unit (Forget ⟪ ψ ⟫))
    recη = ue.η

    recUniq : {N : Category.ob (MOD σeq ℓX)}
      {ρ : FAM S ℓX [ X , Forget ⟅ N ⟆ ]}
      {ψ : MOD σeq ℓX [ freeOb , N ]}
      → ρ ≡ F._⋆_ unit (Forget ⟪ ψ ⟫) → rec ρ ≡ ψ
    recUniq = ue.intro≡

    modExt : {N : Category.ob (MOD σeq ℓX)}
      {ψ ψ' : MOD σeq ℓX [ freeOb , N ]}
      → F._⋆_ unit (Forget ⟪ ψ ⟫) ≡ F._⋆_ unit (Forget ⟪ ψ' ⟫)
      → ψ ≡ ψ'
    modExt = ue.extensionality

  -- `Free` agrees with the free model on objects, and its action on
  -- morphisms is the expected extension of `f` followed by `unit`.
  FreeOb≡ : (X : Category.ob (FAM S ℓX)) → Free ⟅ X ⟆ ≡ FreeFamOb X
  FreeOb≡ X = refl

  FreeHom≡ : {X Y : Category.ob (FAM S ℓX)} (f : FAM S ℓX [ X , Y ])
    → Free ⟪ f ⟫ ≡ FreeMod.rec X (F._⋆_ f (FreeMod.unit Y))
  FreeHom≡ f = refl

  -- The same adjunction in natural-bijection form.  Naturality in the
  -- model is `refl`; naturality in the family is the uniqueness half.
  open NaturalBijection using (_⊣_)

  Free⊣Forget : Free ⊣ Forget
  Free⊣Forget ._⊣_.adjIso {c = X} {d = N} = adjIsoFam X N
  Free⊣Forget ._⊣_.adjNatInD f k = refl
  Free⊣Forget ._⊣_.adjNatInC {c' = X'} {c = X} {d = N} g h =
    FreeMod.modExt X'
      {ψ = Iso.inv (adjIsoFam X' N) (F._⋆_ h g)}
      {ψ' = M._⋆_ {x = FreeFamOb X'} {y = FreeFamOb X} {z = N}
              (Free ⟪ h ⟫) (Iso.inv (adjIsoFam X N) g)}
      refl

  -- ... and hence in unit/counit form, with both triangle identities.
  FreeUnitCounit : UnitCounit._⊣_ Free Forget
  FreeUnitCounit = adj'→adj Free Forget Free⊣Forget

  ⊥Fam : Category.ob (FAM S ℓX)
  ⊥Fam s = ⊥* , isProp→isSet isProp⊥*

  isInitial⊥Fam : isInitial (FAM S ℓX) ⊥Fam
  isInitial⊥Fam Y = (λ s ()) , λ f → funExt (λ s → funExt (λ ()))

  InitialFree : Initial (MOD σeq ℓX)
  InitialFree =
    Free ⟅ ⊥Fam ⟆ ,
    isLeftAdjoint→preservesInitial Free (Forget , Free⊣Forget)
      ⊥Fam isInitial⊥Fam

  InitialFree≅InitialMOD :
    CatIso (MOD σeq ℓX) (Free ⟅ ⊥Fam ⟆) (InitialMOD σeq .fst)
  InitialFree≅InitialMOD =
    initialToIso (MOD σeq ℓX) InitialFree (InitialMOD σeq)
