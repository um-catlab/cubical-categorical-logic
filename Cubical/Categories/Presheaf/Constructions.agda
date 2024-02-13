{-# OPTIONS --safe #-}
module Cubical.Categories.Presheaf.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Bifunctor.Redundant

private
  variable
    ℓ ℓ' ℓS : Level

module _ {C : Category ℓ ℓ'} {ℓS : Level} where
  private
    𝓟 = PresheafCategory C ℓS
  PshProd : Bifunctor 𝓟 𝓟 𝓟
  PshProd = mkBifunctorParAx B where
    open BifunctorParAx
    open Functor
    open NatTrans
    open Category
    Bob : 𝓟 .ob → 𝓟 .ob → 𝓟 .ob
    Bob P Q .F-ob c =  ⟨ P ⟅ c ⟆ ⟩ × ⟨ Q ⟅ c ⟆ ⟩ ,
      isSet× (str (P ⟅ c ⟆)) ((str (Q ⟅ c ⟆)))
    Bob P Q .F-hom f (p , q) = (P .F-hom f p) , (Q .F-hom f q)
    Bob P Q .F-id = funExt (λ (p , q) → ΣPathP ((funExt⁻ (P .F-id) p) , funExt⁻ (Q .F-id) q))
    Bob P Q .F-seq f g =
      funExt λ (p , q) → ΣPathP
        ( (funExt⁻ (P .F-seq f g) p)
        , (funExt⁻ (Q .F-seq f g) q))

    BhomL : ∀ P P' → 𝓟 [ P , P' ] → (Q : 𝓟 .ob) → 𝓟 [ Bob P Q , Bob P' Q ]
    BhomL P P' α Q .N-ob c (p , q) = (α .N-ob c p) , q
    BhomL P P' α Q .N-hom f = funExt λ (p , q) →
      ΣPathP (funExt⁻ (α .N-hom f) _ , refl)

    BhomR : ∀ Q Q' → (P : 𝓟 .ob) → 𝓟 [ Q , Q' ] → 𝓟 [ Bob P Q , Bob P Q' ]
    BhomR Q Q' P β .N-ob c (p , q) = p , (β .N-ob c q)
    BhomR Q Q' P β .N-hom f = funExt λ (p , q) →
      ΣPathP (refl , funExt⁻ (β .N-hom f) _)

    Bhom× : ∀ {P P' Q Q'} → 𝓟 [ P , P' ] → 𝓟 [ Q , Q' ] → 𝓟 [ Bob P Q , Bob P' Q' ]
    Bhom× α β .N-ob c (p , q) = α .N-ob c p , β .N-ob c q
    Bhom× α β .N-hom f = funExt λ (p , q) →
      ΣPathP (funExt⁻ (α .N-hom f) _ , funExt⁻ (β .N-hom f) _)

    B : BifunctorParAx 𝓟 𝓟 𝓟
    B .Bif-ob = Bob
    B .Bif-homL = BhomL _ _
    B .Bif-homR = BhomR _ _
    B .Bif-hom× = Bhom× -- α β .N-ob c (p , q) = α .N-ob c p , β .N-ob c q
    B .Bif-×-id = makeNatTransPath (funExt (λ c → funExt (λ (p , q) → refl)))
    B .Bif-×-seq α α' β β' = makeNatTransPath (funExt (λ c → funExt (λ (p , q) → refl)))
    B .Bif-L×-agree α = makeNatTransPath (funExt (λ c → funExt (λ (p , q) → refl)))
    B .Bif-R×-agree β = makeNatTransPath (funExt (λ c → funExt (λ (p , q) → refl)))
