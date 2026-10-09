-- State algebras as a category displayed over SET, the total category
-- STATEALG of state algebras, displayed state algebras over it, and
-- the strict fibration structure of the latter.
--
-- --lossy-unification is load-bearing for StateAlgᴰFibrationEq: without
-- it unifying the universal element's presheaf does not terminate in
-- practice.
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.StateAlg where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Instances.Functor.Fibration
open import Cubical.Categories.Displayed.Instances.Reindex.Eq.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.StructureOver.Base
open import Cubical.Categories.Displayed.Instances.TotalCategory
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh

open import Cubical.Algebra.State

private
  variable
    ℓ ℓᴰ : Level

open Functorᴰ

-- Since homomorphisms are propositions, state algebras are a
-- StructureOver SET and the category laws come for free.
StateAlgStructure : StructureOver (SET ℓ) ℓ ℓ
StateAlgStructure .StructureOver.ob[_] X = StateAlg ⟨ X ⟩
StateAlgStructure .StructureOver.Hom[_][_,_] f B B' = Homo f B B'
StateAlgStructure .StructureOver.idᴰ = idHomo
StateAlgStructure .StructureOver._⋆ᴰ_ = _⋆Homo_
StateAlgStructure .StructureOver.isPropHomᴰ {y = Y} = isPropHomo (Y .snd)

-- State algebras displayed over SET
STATEALGOver : ∀ ℓ → Categoryᴰ (SET ℓ) ℓ ℓ
STATEALGOver ℓ = StructureOver→Catᴰ (StateAlgStructure {ℓ})

hasPropHomsSTATEALGOver : hasPropHoms (STATEALGOver ℓ)
hasPropHomsSTATEALGOver {c' = Y} _ _ _ = isPropHomo (Y .snd)

STATEALG : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
STATEALG ℓ = ∫C (STATEALGOver ℓ)

StateAlgebra : (ℓ : Level) → Type (ℓ-suc ℓ)
StateAlgebra ℓ = Category.ob (STATEALG ℓ)

StateAlgHom : StateAlgebra ℓ → StateAlgebra ℓ → Type ℓ
StateAlgHom {ℓ} = Category.Hom[_,_] (STATEALG ℓ)

StateAlgForget : Functor (STATEALG ℓ) (SET ℓ)
StateAlgForget = Fst

StateAlgFamilyᴰ : ∀ ℓ ℓᴰ
  → Categoryᴰ (STATEALG ℓ) (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓ ℓᴰ)
StateAlgFamilyᴰ ℓ ℓᴰ =
  EqReindex.reindex (SETᴰ ℓ ℓᴰ) StateAlgForget Eq.refl (λ _ _ → Eq.refl)

StateAlgStructureᴰ : ∀ ℓ ℓᴰ →
  StructureOver (∫C (StateAlgFamilyᴰ ℓ ℓᴰ))
    (ℓ-max ℓ ℓᴰ) (ℓ-max ℓ ℓᴰ)
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.ob[_] (B , Xᴰ) =
  StateAlgᴰ (B .snd) (λ x → ⟨ Xᴰ x ⟩)
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.Hom[_][_,_] (f , fᴰ) Bᴰ Bᴰ' =
  Homoᴰ fᴰ (f .snd) Bᴰ Bᴰ'
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.idᴰ = idHomoᴰ
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver._⋆ᴰ_ {z = (C , Cᴰ)} ϕᴰ ψᴰ =
  ϕᴰ ⋆Homoᴰ ψᴰ
StateAlgStructureᴰ ℓ ℓᴰ .StructureOver.isPropHomᴰ {y = B , Bᴰ} =
  isPropHomoᴰ (λ x → Bᴰ x .snd)

STATEALGᴰ : ∀ ℓ ℓᴰ → Categoryᴰ (STATEALG ℓ)
  (ℓ-max ℓ (ℓ-suc ℓᴰ)) (ℓ-max ℓ ℓᴰ)
STATEALGᴰ ℓ ℓᴰ =
  ∫Cᴰ (StateAlgFamilyᴰ ℓ ℓᴰ) $ StructureOver→Catᴰ $ StateAlgStructureᴰ ℓ ℓᴰ

-- manual here is better than using Fstᴰ because it avoids a composition
StateAlgForgetᴰ : Functorᴰ StateAlgForget (STATEALGᴰ ℓ ℓᴰ) (SETᴰ ℓ ℓᴰ)
StateAlgForgetᴰ .F-obᴰ Bᴰ = Bᴰ .fst
StateAlgForgetᴰ .F-homᴰ fᴰ = fᴰ .fst
StateAlgForgetᴰ .F-idᴰ = refl
StateAlgForgetᴰ .F-seqᴰ fᴰ gᴰ = refl

-- STATEALG is strictly unital and associative, and displayed state
-- algebras form a fibration over it in the strict sense.
StateAlgIdL : ∀ ℓ → EqPsh.EqIdL (STATEALG ℓ)
StateAlgIdL ℓ _ = Eq.refl

StateAlgIdR : ∀ ℓ → EqPsh.EqIdR (STATEALG ℓ)
StateAlgIdR ℓ _ = Eq.refl

StateAlgAssoc : ∀ ℓ → EqPsh.ReprEqAssoc (STATEALG ℓ)
StateAlgAssoc ℓ _ _ _ _ _ Eq.refl = Eq.refl

StateAlgᴰFibrationEq : ∀ ℓ →
  EqPsh.Fibration (STATEALGᴰ ℓ ℓ) (StateAlgAssoc ℓ)
StateAlgᴰFibrationEq ℓ {x = Z} {y = B'} f Bᴰ' =
  EqPsh.UEⱽ→Reprⱽ _ (StateAlgIdR ℓ) ue
  where
  pullᴰ : Categoryᴰ.ob[_] (STATEALGᴰ ℓ ℓ) Z
  pullᴰ .fst z = Bᴰ' .fst (f .fst z)
  pullᴰ .snd = pull (f .snd) (Bᴰ' .snd) (B' .fst .snd)

  ue : EqPsh.CartesianLiftUE (STATEALGᴰ ℓ ℓ)
    (StateAlgAssoc ℓ) (StateAlgIdR ℓ) f Bᴰ'
  ue .EqPsh.UEⱽ.v = pullᴰ
  ue .EqPsh.UEⱽ.e .fst _ zᴰ = zᴰ
  ue .EqPsh.UEⱽ.e .snd =
    π-pull (f .snd) (Bᴰ' .snd) (B' .fst .snd)
  ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
    (Y , Yᴰ , g) .fst h .fst = h .fst
  ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
    (Y , Yᴰ , g) .fst h .snd =
      pull-intro (f .snd) (Bᴰ' .snd) (B' .fst .snd) (g .snd) (h .snd)
  ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
    (Y , Yᴰ , g) .snd .fst h =
      ∫Homoᴰ≡ _ h (λ x → Bᴰ' .fst x .snd) refl
  ue .EqPsh.UEⱽ.universal .isPshIsoEq.nIso
    (Y , Yᴰ , g) .snd .snd h =
      ∫Homoᴰ≡ _ h (λ y → Bᴰ' .fst (f .fst y) .snd) refl

StateAlgᴰEqFibrationData : ∀ ℓ → EqFibrationData (STATEALGᴰ ℓ ℓ)
StateAlgᴰEqFibrationData ℓ .Eq-idL = StateAlgIdL ℓ
StateAlgᴰEqFibrationData ℓ .Eq-idR = StateAlgIdR ℓ
StateAlgᴰEqFibrationData ℓ .Eq-assoc = StateAlgAssoc ℓ
StateAlgᴰEqFibrationData ℓ .Eq-fibration = StateAlgᴰFibrationEq ℓ
