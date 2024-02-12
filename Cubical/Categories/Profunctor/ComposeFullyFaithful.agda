{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.ComposeFullyFaithful where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function hiding (_∘_)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc; cong-∙)
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties


private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    E : Category ℓE ℓE'

open Category
open Functor

module _ {F : Functor C D} {G : Functor D E}
  (isFullyFaithfulF : isFullyFaithful F)
  (isFullyFaithfulG : isFullyFaithful G)
  where

  -- isFullG : isFull G
  -- isFullG = isFullyFaithful→Full {F = G} isFullyFaithfulG

  -- isFaithfulG : isFaithful G
  -- isFaithfulG = isFullyFaithful→Faithful {F = G} isFullyFaithfulG

  -- isFullF : isFull F
  -- isFullF = isFullyFaithful→Full {F = F} isFullyFaithfulF

  -- isFaithfulF : isFaithful F
  -- isFaithfulF = isFullyFaithful→Faithful {F = F} isFullyFaithfulF

  -- isFullG∘F : isFull (G ∘F F)
  -- isFullG∘F x y G∘F[f] = {!!}

  -- isFaithfulG∘F : isFaithful (G ∘F F)
  -- isFaithfulG∘F = {!!}

  isFullyFaithfulG∘F : isFullyFaithful (G ∘F F)
  isFullyFaithfulG∘F x y =
    equivIsEquiv
      (compEquiv (_ , isFullyFaithfulF x y)
                 (_ , isFullyFaithfulG (F ⟅ x ⟆) (F ⟅ y ⟆)))
