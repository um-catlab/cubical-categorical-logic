module Cubical.Categories.Instances.Sets.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category renaming (pathToIso to catPathToIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Presheaf

open import Cubical.Categories.2Category.Base
open import Cubical.Categories.2Functor.Base
open import Cubical.Categories.2Functor.Fibration

open 2Category
open LaxFunctor
open PseudoFunctor
open isPseudo
open isIso2Cell
open GroupoidObjectsCategory
open isUnivalent
open Functor
open NatTrans

private
  variable
    ℓ ℓ' : Level

module _ ℓ ℓ' where
  SetsFibration-lax :
    LaxFunctor (Cat→2CatEq (SET ℓ ^op))
      (CAT {ℓC = ℓ-max ℓ (ℓ-suc ℓ')} {ℓC' = ℓ-max ℓ ℓ'})
  SetsFibration-lax .F₀ A .cat .Category.ob = ⟨ A ⟩ → hSet ℓ'
  SetsFibration-lax .F₀ A .cat .Category.Hom[_,_] B B' =
    ∀ (a : ⟨ A ⟩) → ⟨ B a ⟩ → ⟨ B' a ⟩
  SetsFibration-lax .F₀ A .cat .Category.id = λ a z → z
  SetsFibration-lax .F₀ A .cat .Category._⋆_ = λ f g a z₁ → g a (f a z₁)
  SetsFibration-lax .F₀ A .cat .Category.⋆IdL = λ _ → refl
  SetsFibration-lax .F₀ A .cat .Category.⋆IdR = λ _ → refl
  SetsFibration-lax .F₀ A .cat .Category.⋆Assoc = λ _ _ _ → refl
  SetsFibration-lax .F₀ A .cat .Category.isSetHom {y = y} =
    isSetΠ λ _ → isSetΠ λ _ → y _ .snd
  SetsFibration-lax .F₀ A .groupoid-obs = isGroupoidΠ λ _ → isGroupoidHSet
  SetsFibration-lax .F₁ f .F-ob = λ z z₁ → z (f z₁)
  SetsFibration-lax .F₁ f .F-hom = λ z a → z (f a)
  SetsFibration-lax .F₁ f .F-id = refl
  SetsFibration-lax .F₁ f .F-seq = λ _ _ → refl
  SetsFibration-lax .F₂ Eq.refl = idTrans _
  SetsFibration-lax .F-id .N-ob = λ x₁ a z → z
  SetsFibration-lax .F-id .N-hom = λ _ → refl
  SetsFibration-lax .F-seq f g .N-ob = λ x₁ a z₁ → z₁
  SetsFibration-lax .F-seq f g .N-hom = λ _ → refl
  SetsFibration-lax .F-id₂ = refl
  SetsFibration-lax .F-seqⱽ Eq.refl Eq.refl = makeNatTransPath refl
  SetsFibration-lax .F-seqᴴ Eq.refl Eq.refl = makeNatTransPath refl
  SetsFibration-lax .F-unitality-l _ = makeNatTransPathP _ _ refl
  SetsFibration-lax .F-unitality-r _ = makeNatTransPathP _ _ refl
  SetsFibration-lax .F-associativity _ _ _ = makeNatTransPathP _ _ refl

  SetsFibration-pseudo-F-id-iso : ∀ {A : hSet ℓ}
    → isIso2Cell CAT {x = SetsFibration-lax .F₀ A} {y = SetsFibration-lax .F₀ A}
      (SetsFibration-lax .F-id {A})
  SetsFibration-pseudo-F-id-iso .inv .N-ob = λ x a z → z
  SetsFibration-pseudo-F-id-iso .inv .N-hom = λ _ → refl
  SetsFibration-pseudo-F-id-iso .sec = makeNatTransPath refl
  SetsFibration-pseudo-F-id-iso .ret = makeNatTransPath refl

  SetsFibration-pseudo : isPseudo SetsFibration-lax
  SetsFibration-pseudo .F-id-iso {x} = SetsFibration-pseudo-F-id-iso {x}
  SetsFibration-pseudo .F-seq-iso f g .inv .N-ob = λ x₁ a z₁ → z₁
  SetsFibration-pseudo .F-seq-iso f g .inv .N-hom = λ _ → refl
  SetsFibration-pseudo .F-seq-iso f g .sec = makeNatTransPath refl
  SetsFibration-pseudo .F-seq-iso f g .ret = makeNatTransPath refl

  -- Separating the definition of the component definitions, specifically
  -- the isPseudo proof, to convince Agda that this definition is terminating
  SetsFibration : FibrationEq (SET ℓ) _ _
  SetsFibration .lax = SetsFibration-lax
  SetsFibration .pseudo = SetsFibration-pseudo
