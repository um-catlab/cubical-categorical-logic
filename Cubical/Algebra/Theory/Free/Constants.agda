-- Freeness as initiality.
--
-- The free model on V is the initial model of σ ⊕ Pointed V, where
-- `Pointed V` is the theory of a set with a marked point for each v : V.
-- Coproduct rather than tensor is the point: the generators are subject
-- to no interaction with σ's operations beyond σ's own equations.
module Cubical.Algebra.Theory.Free.Constants where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥; ⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Initial

open import Cubical.Algebra.Theory
open import Cubical.Algebra.Theory.Category
open import Cubical.Algebra.Theory.Theories
open import Cubical.Algebra.Theory.Constructions
open import Cubical.Algebra.Theory.Free.Explicit
open import Cubical.Algebra.Theory.Free.Section

private
  variable
    ℓ ℓ'' ℓv ℓX : Level

open AlgTheorySig

PointedSig : (V : Type ℓv) → AlgTheorySig ℓv ℓv
PointedSig V .ops = V
PointedSig V .arities _ = ⊥*

Pointed : (V : Type ℓv) → AlgTheoryEqns (PointedSig V) ℓ-zero ℓv
Pointed V .AlgTheoryEqns.eqns = ⊥
Pointed V .AlgTheoryEqns.vars ()
Pointed V .AlgTheoryEqns.lhs ()
Pointed V .AlgTheoryEqns.rhs ()

module _ {V : Type ℓv} {X : Type ℓX} where
  pointsOf : Alg (Pointed V) X → V → X
  pointsOf P v = Alg.⟨_⟩⟦_⟧op P v (λ ())

  mkPoints : (V → X) → Alg (Pointed V) X
  mkPoints ρ .Alg.⟨_⟩⟦_⟧op v _ = ρ v
  mkPoints ρ .Alg.⟦_⟧eqn ()

-- Adjoining constants.  `T [ X ]adjoin` is `T` with a constant adjoined for
-- every element of `X`: the coproduct of `T` with the pointed theory
-- on `X`.
infixl 30 _[_]adjoin
_[_]adjoin : {σ : AlgTheorySig ℓ ℓv} (σeq : AlgTheoryEqns σ ℓ'' ℓv)
  (V : Type ℓv) → AlgTheoryEqns (σ ⊕Sig PointedSig V) (ℓ-max ℓ'' ℓ-zero) ℓv
σeq [ V ]adjoin = σeq ⊕Eqns Pointed V

module _ {σ : AlgTheorySig ℓ ℓv} (σeq : AlgTheoryEqns σ ℓ'' ℓv)
  (V : Type ℓv) where

  private
    ℓF = ℓFree ℓ ℓ'' ℓv

  module _ (X : hSet ℓX) where
    modelIso : Iso (Alg (σeq [ V ]adjoin) ⟨ X ⟩) (Alg σeq ⟨ X ⟩ × Alg (Pointed V) ⟨ X ⟩)
    modelIso = ⊕AlgIso σeq (Pointed V) X

    withPoints : Alg σeq ⟨ X ⟩ → (V → ⟨ X ⟩) → Alg (σeq [ V ]adjoin) ⟨ X ⟩
    withPoints B ρ = Iso.inv modelIso (B , mkPoints ρ)

    forgetPoints : Alg (σeq [ V ]adjoin) ⟨ X ⟩ → Alg σeq ⟨ X ⟩
    forgetPoints N = Iso.fun modelIso N .fst

    pointsAt : Alg (σeq [ V ]adjoin) ⟨ X ⟩ → V → ⟨ X ⟩
    pointsAt N = pointsOf (Iso.fun modelIso N .snd)

  FreeAlg[V] : Alg (σeq [ V ]adjoin) (FreeModel σeq V)
  FreeAlg[V] = withPoints (FreeModel σeq V , trunc) (FreeAlg σeq V) var

  FreeOb[V] : Category.ob (MOD (σeq [ V ]adjoin) ℓF)
  FreeOb[V] = (FreeModel σeq V , trunc) , FreeAlg[V]

  module _ (N : Category.ob (MOD (σeq [ V ]adjoin) ℓF)) where
    private
      Xh = N .fst
      isSetX = N .fst .snd
      Nσ = forgetPoints Xh (N .snd)
      Nρ = pointsAt Xh (N .snd)

    restHomo : {f : FreeModel σeq V → ⟨ Xh ⟩}
      → Homo (σeq [ V ]adjoin) f FreeAlg[V] (N .snd) → Homo σeq f (FreeAlg σeq V) Nσ
    restHomo ϕ .Homo.op-hom op x y eq = Homo.op-hom ϕ (inl op) x y eq

    genβ : {f : FreeModel σeq V → ⟨ Xh ⟩}
      → Homo (σeq [ V ]adjoin) f FreeAlg[V] (N .snd) → ∀ v → f (var v) ≡ Nρ v
    genβ ϕ v =
      Homo.op-hom ϕ (inr v) (λ ()) (var v) refl
      ∙ cong (Alg.⟨_⟩⟦_⟧op (N .snd) (inr v)) (funExt (λ ()))

    recC : FreeModel σeq V → ⟨ Xh ⟩
    recC = rec σeq isSetX Nσ Nρ

    recHomoC : Homo (σeq [ V ]adjoin) recC FreeAlg[V] (N .snd)
    recHomoC .Homo.op-hom (inl op) x y eq =
      Homo.op-hom (recHomo σeq isSetX Nσ Nρ) op x y eq
    recHomoC .Homo.op-hom (inr v) x y eq =
      cong recC eq ∙ cong (Alg.⟨_⟩⟦_⟧op (N .snd) (inr v)) (funExt (λ ()))

    isContrHom[V] : isContr (ModHom (σeq [ V ]adjoin) ℓF FreeOb[V] N)
    isContrHom[V] .fst = recC , recHomoC
    isContrHom[V] .snd (f , ϕ) =
      Σ≡Prop (λ _ → isPropHomo (σeq [ V ]adjoin) isSetX)
        (funExt (λ x →
          sym (recUniq σeq isSetX Nσ Nρ f (restHomo ϕ) (genβ ϕ) x)))

  isInitialFreeOb[V] : isInitial (MOD (σeq [ V ]adjoin) ℓF) FreeOb[V]
  isInitialFreeOb[V] = isContrHom[V]

  InitialMOD[V] : Initial (MOD (σeq [ V ]adjoin) ℓF)
  InitialMOD[V] = FreeOb[V] , isInitialFreeOb[V]
