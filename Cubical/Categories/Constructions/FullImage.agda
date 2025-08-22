{-

The Full Image of a Functor

-}
module Cubical.Categories.Constructions.FullImage where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Functions.Embedding
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PropTrunc

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.FullSubcategory

private
  variable
    ℓC ℓC' ℓD ℓD' : Level


open Category
open Functor

module _
  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D) where

  FullImage : Category ℓC ℓD'
  FullImage .ob = C .ob
  FullImage .Hom[_,_] c c' = D [ F ⟅ c ⟆ , F ⟅ c' ⟆ ]
  FullImage .id = D .id
  FullImage ._⋆_ = D ._⋆_
  FullImage .⋆IdL = D .⋆IdL
  FullImage .⋆IdR = D .⋆IdR
  FullImage .⋆Assoc = D .⋆Assoc
  FullImage .isSetHom = D .isSetHom

  ToFullImage : Functor C FullImage
  ToFullImage .F-ob = λ z → z
  ToFullImage .F-hom = F-hom F
  ToFullImage .F-id = F-id F
  ToFullImage .F-seq = F-seq F

  FromFullImage : Functor FullImage D
  FromFullImage .F-ob = F-ob F
  FromFullImage .F-hom = λ z → z
  FromFullImage .F-id = refl
  FromFullImage .F-seq f g = refl

  CompFullImage : (FromFullImage ∘F ToFullImage ≡ F)
  CompFullImage = Functor≡ (λ _ → refl) (λ _ → refl)

module _
  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  (isFullyFaithfulF : isFullyFaithful F)
  where
  private
    FC = FullImage F
    FF≃  : ∀ {x y} → C [ x , y ] ≃ D [ _ , _ ]
    FF≃ = _ , (isFullyFaithfulF _ _)

  inv : Functor FC C
  inv .F-ob = λ z → z
  inv .F-hom = invIsEq (isFullyFaithfulF _ _)
  inv .F-id = sym (invEq (equivAdjointEquiv FF≃) (F .F-id))
  inv .F-seq f g =
    sym (invEq (equivAdjointEquiv FF≃)
    (F .F-seq _ _ ∙ cong₂ (seq' D) (secEq FF≃ _) (secEq FF≃ _)))
