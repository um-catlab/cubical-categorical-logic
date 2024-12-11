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
open import Cubical.Categories.Bifunctor.Redundant

private
  variable
    ℓ ℓ' ℓA ℓB : Level

open Functor
module _ {C : Category ℓ ℓ'} {ℓA ℓB : Level} where
  _×𝓟_ : Presheaf C ℓA → Presheaf C ℓB → Presheaf C (ℓ-max ℓA ℓB)
  (P ×𝓟 Q) .F-ob c .fst = ⟨ P ⟅ c ⟆ ⟩ × ⟨ Q ⟅ c ⟆ ⟩
  (P ×𝓟 Q) .F-ob c .snd = isSet× (str (P ⟅ c ⟆)) ((str (Q ⟅ c ⟆)))
  (P ×𝓟 Q) .F-hom f (p , q) = (P .F-hom f p) , (Q .F-hom f q)
  (P ×𝓟 Q) .F-id =
      funExt (λ (p , q) → ΣPathP ((funExt⁻ (P .F-id) p) , funExt⁻ (Q .F-id) q))
  (P ×𝓟 Q) .F-seq f g =
      funExt λ (p , q) → ΣPathP
        ( (funExt⁻ (P .F-seq f g) p)
        , (funExt⁻ (Q .F-seq f g) q))
  private
    𝓟 = PresheafCategory C ℓA
    𝓠 = PresheafCategory C ℓB
    𝓡 = PresheafCategory C (ℓ-max ℓA ℓB)

  PshProd : Bifunctor 𝓟 𝓠 𝓡
  PshProd = mkBifunctorPar B where
    open BifunctorPar
    open NatTrans
    open Category

    Bhom× :
      ∀ {P P' Q Q'} →
      𝓟 [ P , P' ] →
      𝓠 [ Q , Q' ] →
      𝓡 [ P ×𝓟 Q , P' ×𝓟 Q' ]
    Bhom× α β .N-ob c (p , q) = α .N-ob c p , β .N-ob c q
    Bhom× α β .N-hom f = funExt λ (p , q) →
      ΣPathP (funExt⁻ (α .N-hom f) _ , funExt⁻ (β .N-hom f) _)

    B : BifunctorPar 𝓟 𝓠 𝓡
    B .Bif-ob = _×𝓟_
    B .Bif-hom× = Bhom×
    B .Bif-×-id =
      makeNatTransPath (funExt (λ c → funExt (λ (p , q) → refl)))
    B .Bif-×-seq α α' β β' =
      makeNatTransPath (funExt (λ c → funExt (λ (p , q) → refl)))

  private
    open Category
    open Bifunctor
    open NatTrans
    -- Test to make sure we get the right definitional
    -- behavior for Bif-homL, Bif-homR
    module _ (P P' : 𝓟 .ob)(Q Q' : 𝓠 .ob)
             (α : 𝓟 [ P , P' ]) (β : 𝓠 [ Q , Q' ]) c where

      _ : PshProd .Bif-homL α Q .N-ob c ≡ λ (p , q) → α .N-ob c p , q
      _ = refl

      _ : PshProd .Bif-homR P β .N-ob c ≡ λ (p , q) → p , β .N-ob c q
      _ = refl

