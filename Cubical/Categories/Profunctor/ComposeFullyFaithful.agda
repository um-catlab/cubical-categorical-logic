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

module _ {F : Functor C D} {G : Functor D E} where

  module _
    (isFullyFaithfulF : isFullyFaithful F)
    (isFullyFaithfulG : isFullyFaithful G)
    where
    isFullyFaithfulG∘F : isFullyFaithful (G ∘F F)
    isFullyFaithfulG∘F x y =
      equivIsEquiv
        (compEquiv (_ , isFullyFaithfulF x y)
                 (_ , isFullyFaithfulG (F ⟅ x ⟆) (F ⟅ y ⟆)))

  module _
    (isFullG : isFull G)
    (isFullF : isFull F)
    where
    isFullG∘F : isFull (G ∘F F)
    isFullG∘F x y G∘F[f] =
      rec
        isPropPropTrunc
        (λ Ff → rec
          isPropPropTrunc
          (λ f → ∣ f .fst , cong (G .F-hom) (f .snd) ∙ Ff .snd ∣₁)
          (isFullF x y (Ff .fst)))
        (isFullG (F ⟅ x ⟆) (F ⟅ y ⟆) G∘F[f])

  module _
    (isFaithfulF : isFaithful F)
    (isFaithfulG : isFaithful G)
    where

    isFaithfulG∘F : isFaithful (G ∘F F)
    isFaithfulG∘F x y =
      isEmbedding→Inj
        (compEmbedding
        ((λ v → F-hom G v) ,
          (injEmbedding (E .isSetHom) (isFaithfulG (F ⟅ x ⟆) (F ⟅ y ⟆) _ _)))
        ((λ z → F-hom F z) ,
          (injEmbedding (D .isSetHom) (isFaithfulF x y _ _))) .snd)
