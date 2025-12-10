{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Uncurried where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open Category
open Functor
open NatTrans
open Categoryᴰ

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' : Level

module _
  (C : Category ℓC ℓC')
  (ℓP ℓPᴰ : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
  PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰ
  PRESHEAFᴰ .idᴰ = idPshHomᴰ
  PRESHEAFᴰ ._⋆ᴰ_ = {!_⋆PshHomᴰ_!}
  PRESHEAFᴰ .⋆IdLᴰ = {!!}
  PRESHEAFᴰ .⋆IdRᴰ = {!!}
  PRESHEAFᴰ .⋆Assocᴰ = {!!}
  PRESHEAFᴰ .isSetHomᴰ = {!!}
  -- PRESHEAFᴰ .ob[_] = Presheafᴰ
  -- PRESHEAFᴰ .Hom[_][_,_] = NatTransᴰ
  -- PRESHEAFᴰ .idᴰ = idTransᴰ
  -- PRESHEAFᴰ ._⋆ᴰ_ = seqTransᴰ
  -- PRESHEAFᴰ .⋆IdLᴰ {x = P} {y = Q} {f = α} {xᴰ = Pᴰ} {yᴰ = Qᴰ} αᴰ =
  --   makeNatTransPathP refl
  --   (congS (λ x → Qᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆IdL _))
  --   refl
  -- PRESHEAFᴰ .⋆IdRᴰ {x = P} {y = Q} {f = α} {xᴰ = Pᴰ} {yᴰ = Qᴰ} αᴰ =
  --   makeNatTransPathP refl
  --   (congS (λ x → Qᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆IdR _))
  --   refl
  -- PRESHEAFᴰ .⋆Assocᴰ {wᴰ = Sᴰ} αᴰ βᴰ γᴰ = makeNatTransPathP refl
  --   (congS (λ x → Sᴰ ∘F (∫ᴾ⇒ x ^opF)) (PresheafCategory _ _ .⋆Assoc _ _ _))
  --   refl
  -- PRESHEAFᴰ .isSetHomᴰ = isSetNatTrans
