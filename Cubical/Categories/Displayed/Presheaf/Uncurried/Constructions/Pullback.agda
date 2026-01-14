{-# OPTIONS --lossy-unification #-}
{- TODO: split up this file into a bunch of individual construction files -}

{-

  Every construction on presheaves should come with
  1. A UMP which provides an interface to it
  2. A reindexing lemma that shows that it commutes with reindPshᴰNatTrans in the appropriate sense

-}

module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Pullback where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Sigma.More as Type
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Reind
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.Constant.More
open import Cubical.Categories.FunctorComprehension.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory as TotalCat hiding (intro)
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions hiding (ΣPsh)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions.RightAdjoint
open import Cubical.Categories.Profunctor.Constructions.Extension
open import Cubical.Categories.Yoneda.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
import Cubical.Categories.Displayed.Presheaf.Constructions.Curry as Curry
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Sigma
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Path
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Push

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓS ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ ℓSᴰ : Level

open Category
open Functor
open Functorᴰ
open Iso
open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} where
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
    (α : PshHom P R)
    (β : PshHom Q R)
    where
    Pullback : Presheaf C _
    Pullback =
      reindPsh (TotalCat.intro Id ttS) (PresheafᴰNotation.∫ (Unitᴰ C) (P ×Psh Q) (reindPshᴰNatTrans (α ×PshHom β) (PathPsh R)))

    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module R = PresheafNotation R
      module PB = PresheafNotation Pullback

    module _ {S : Presheaf C ℓS}
      (α' : PshHom S Q) (β' : PshHom S P)
      where
      private
        module S = PresheafNotation S
      isPullbackSq : Type _
      isPullbackSq =
        Σ[ comm ∈ (α' ⋆PshHom β) ≡ (β' ⋆PshHom α) ]
        ∀ Γ (q : Q.p[ Γ ]) → isIso {A = Σ[ s ∈ S.p[ Γ ] ] q ≡ α' .N-ob Γ s}{B = Σ[ p ∈ P.p[ Γ ] ] β .N-ob Γ q ≡ α .N-ob Γ p}
        λ (s , α's≡q) → (β' .N-ob Γ s) , cong (β .N-ob Γ) α's≡q ∙ funExt₂⁻ (cong N-ob comm) Γ s

      module _ ((_ , ispb) : isPullbackSq) {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)where
        private
          module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
        BeckChevalley-ptwise : ∀ Γ Γᴰ (q : Q.p[ Γ ])
          → Iso (Σ[ s ∈ S.p[ Γ ] ] Pᴰ.p[ β' .N-ob Γ s ][ Γᴰ ] × (q ≡ α' .N-ob Γ s))
                (Σ[ p ∈ P.p[ Γ ] ] Pᴰ.p[ p ][ Γᴰ ] × (β .N-ob Γ q ≡ α .N-ob Γ p))
        BeckChevalley-ptwise Γ Γᴰ q =
          compIso (invIso Σ-assoc-Iso) $
          compIso Σ-assoc-swap-Iso $
          compIso (Σ-cong-iso-fst (isIsoToIso (ispb Γ q))) $
          compIso Σ-assoc-swap-Iso $
          Σ-assoc-Iso

        opaque
          unfolding Element ΣPsh PathPsh push-σ PshHet→ElementFunctorᴰ PshHomᴰ-map-toElt
            PresheafᴰNotation.⋆IdLᴰ makePshHomᴰPath Curry.UncurryPshᴰ Curry.CurryPshᴰ
          BeckChevalley : PshIsoⱽ (push α' (reindPshᴰNatTrans β' Pᴰ)) (reindPshᴰNatTrans β (push α Pᴰ))
          BeckChevalley = Isos→PshIso (λ (Γ , Γᴰ , q) → BeckChevalley-ptwise Γ Γᴰ q)
            λ (Δ , Δᴰ , q) (Γ , Γᴰ , q') (γ , γᴰ , γ⋆q≡q') (s , pᴰ , q'≡α's) →
            ΣPathP ((β' .N-hom Δ Γ γ s) , ΣPathPProp (λ _ → R.isSetPsh _ _)
            (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.⋆ᴰ-reind _ _ _ ∙ (sym $ Pᴰ.⋆ᴰ-reind _ _ _)))

opaque
  unfolding unfoldPresheafᴰDefs BeckChevalley
  unfoldPullbackDefs : Unit
  unfoldPullbackDefs = tt
