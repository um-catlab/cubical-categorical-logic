{-

  Any profunctor C → D can be extend to a functor Psh C → Psh D that agrees with the original on representables.
  This is part of the fact that Psh C is a free cocompletion of C

  This is also the extension part of a 2-monad structure on Psh

-}

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Profunctor.Constructions.Extension where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Yoneda.More

private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS : Level

open Category
open Bifunctor
open Functor
open NatTrans
open PshHom
open PshIso

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} where
  module ext-⊗ {ℓP}{ℓQ} (P : Bifunctor (D ^op) C (SET ℓP)) (Q : Presheaf C ℓQ){d} =
    Tensor (CurryBifunctor P ⟅ d ⟆) Q

  -- TODO: make this a bifunctor
  ext : Bifunctor (D ^op) C (SET ℓP)
    → Functor (PresheafCategory C ℓ) (PresheafCategory D (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓ))
  ext P = CurryBifunctor $ Sym $ ⊗-Bif ∘Fl CurryBifunctor P
  private
    test-ext : ∀ (P : Bifunctor (D ^op) C (SET ℓP)) (Q : Presheaf C ℓQ) d
      → ⟨ (ext P ⟅ Q ⟆) .F-ob d ⟩ ≡ ((CurryBifunctor P ⟅ d ⟆) ⊗ Q)
    test-ext P Q d = refl


  CoContinuous : {ℓP : Level → Level}
    (P : ∀ {ℓ} → Functor (PresheafCategory C ℓ) (PresheafCategory D (ℓP ℓ)))
    → Typeω
  CoContinuous P = ∀ {ℓ} (Q : Presheaf C ℓ)
    → PshIso (P ⟅ Q ⟆) (ext (CurriedToBifunctorL (P ∘F CurryBifunctorL (HomBif C))) ⟅ Q ⟆)

module _ {C : Category ℓC ℓC'} where
  private
    test-ext' : ∀ (Q : Presheaf C ℓQ) →
      ext (HomBif C) ⟅ Q ⟆ ≡ ◇ Q
    test-ext' Q = refl
