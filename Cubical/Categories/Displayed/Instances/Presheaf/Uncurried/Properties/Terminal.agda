{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Properties.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.More
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
import Cubical.Categories.Displayed.Presheaf.Constructions.Curry as Curry
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Base

open Category
open Functor
open PshHom
open PshIso
open Categoryᴰ


module _
  {ℓC ℓC' ℓCᴰ ℓCᴰ'}
  (C : Category ℓC ℓC')
  (ℓP ℓPᴰ : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where

  private
    PSHᴰ = PRESHEAFᴰ C ℓP ℓPᴰ Cᴰ
    module PSHᴰ = Fibers PSHᴰ

  TerminalsⱽPSHᴰ : Terminalsⱽ PSHᴰ
  TerminalsⱽPSHᴰ P =
    UniversalElementⱽ'.REPRⱽ
      (record {
        vertexⱽ = Unit*Psh
      ; elementⱽ = _
      ; universalⱽ = λ x →
          IsoToIsIso
            (iso (λ _ → tt)
                 (λ _ → the-intro x)
                 (λ _ → refl)
                 (the-intro≡ x)) })
      where
      module よ1 = PresheafNotation (PSHᴰ [-][-, Unit*Psh ])
      opaque
        unfolding unfoldPresheafᴰDefs Curry.unfoldCurryDefs
        the-intro : (x : (PSHᴰ / (PRESHEAF C ℓP [-, P ])) .ob) → よ1.p[ x ]
        the-intro (P , Pᴰ , α) = pshhom (λ c _ → tt*) (λ _ _ _ _ → refl)

        the-intro≡ :
          (x : (PSHᴰ / (PRESHEAF C ℓP [-, P ])) .ob) →
          retract (λ _ → tt) (λ _ → the-intro x)
        the-intro≡ _ _ = makePshHomPath refl
