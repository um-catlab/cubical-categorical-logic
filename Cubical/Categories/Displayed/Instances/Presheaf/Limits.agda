{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Elements
open import Cubical.Categories.Presheaf.CCC

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianV
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf hiding (PRESHEAFᴰ)
open import Cubical.Categories.Displayed.Instances.Presheaf.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Properties

open Category
open Functor
open NatTrans
open Contravariant
open Categoryᴰ
open UniversalElement
open UniversalElementⱽ
open isIsoOver
private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _ (C : Category ℓC ℓC') (ℓS ℓSᴰ : Level) where
  private
    module 𝓟ᴰ = Categoryᴰ (PRESHEAFᴰ C ℓS ℓSᴰ)
  opaque
    TerminalsⱽPRESHEAFᴰ : Terminalsⱽ (PRESHEAFᴰ C ℓS ℓSᴰ)
    TerminalsⱽPRESHEAFᴰ P .vertexⱽ = ⊤𝓟 _ _ .vertex -- ⊤𝓟 _ ℓSᴰ .fst
    TerminalsⱽPRESHEAFᴰ P .elementⱽ = tt
    TerminalsⱽPRESHEAFᴰ P .universalⱽ .fst x =
      natTrans (λ _ _ → tt*) (λ _ → refl)
    TerminalsⱽPRESHEAFᴰ P .universalⱽ .snd .fst _ = refl
    TerminalsⱽPRESHEAFᴰ P .universalⱽ .snd .snd a =
      makeNatTransPathP refl refl refl

    opaque
      unfolding hSetReasoning.reind
      BinProductsⱽPRESHEAFᴰ : BinProductsⱽ (PRESHEAFᴰ C ℓS ℓSᴰ)
      BinProductsⱽPRESHEAFᴰ _ (Pᴰ , Pᴰ') .vertexⱽ = ×𝓟 _ _ (Pᴰ , Pᴰ') .vertex
      BinProductsⱽPRESHEAFᴰ _ (Pᴰ , Pᴰ') .elementⱽ =
        (seqTrans (×𝓟 _ _ (Pᴰ , Pᴰ') .element .fst) (idTransᴰ _ _ _))
        , (seqTrans (×𝓟 _ _ (Pᴰ , Pᴰ') .element .snd) (idTransᴰ _ _ _))
      BinProductsⱽPRESHEAFᴰ _ (Pᴰ , Pᴰ') .universalⱽ .fst (id∘αᴰ , id∘αᴰ') =
        natTrans
        (λ (x , x') q → ((id∘αᴰ ⟦ _ ⟧) q) , (id∘αᴰ' ⟦ _ ⟧) q)
        λ (f , f-comm) → funExt λ q →
        ΣPathP (funExt⁻ (id∘αᴰ .N-hom _) _ , funExt⁻ (id∘αᴰ' .N-hom _) _)
      BinProductsⱽPRESHEAFᴰ _ (Pᴰ , Pᴰ') .universalⱽ .snd .fst (id∘αᴰ , id∘αᴰ') =
        ΣPathP
        ( makeNatTransPath (sym (transport-filler _ _))
        , makeNatTransPath (sym (transport-filler _ _)))
      BinProductsⱽPRESHEAFᴰ _ (Pᴰ , Pᴰ') .universalⱽ {y = Q}{yᴰ = Qᴾ}{f = α}
        .snd .snd αᴰ = makeNatTransPath (funExt λ q → funExt λ q' →
        ΣPathP
        ( fromPathP
        (λ i → αᴰ .N-ob
          (transport-filler (λ j → Σ (ob C) (λ c → fst (F-ob Q c))) q (~ i))
          (transport-filler
            (λ j →
              Qᴾ .F-ob (transp (λ j₁ → Σ (ob C) (λ c → fst (F-ob Q c))) (~ j) q)
                .fst)
            q' (~ i)) .fst)
        , fromPathP
        (λ i → αᴰ .N-ob
          (transport-filler (λ j → Σ (ob C) (λ c → fst (F-ob Q c))) q (~ i))
          (transport-filler
            (λ j →
              Qᴾ .F-ob
                (transp (λ j₁ → Σ (ob C) (λ c → fst (F-ob Q c))) (~ j) q) .fst)
            q' (~ i)) .snd)))
  𝓟-CCⱽ : CartesianCategoryⱽ (PresheafCategory C ℓS) _ _
  𝓟-CCⱽ .CartesianCategoryⱽ.Cᴰ = (PRESHEAFᴰ C ℓS ℓSᴰ)
  𝓟-CCⱽ .CartesianCategoryⱽ.termⱽ = TerminalsⱽPRESHEAFᴰ
  𝓟-CCⱽ .CartesianCategoryⱽ.bpⱽ = BinProductsⱽPRESHEAFᴰ
  𝓟-CCⱽ .CartesianCategoryⱽ.cartesianLifts = isFibrationPRESHEAFᴰ _ _ _
