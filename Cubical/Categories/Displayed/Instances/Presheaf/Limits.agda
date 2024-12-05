{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.CCC

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Properties

open Category
open Functor
open NatTrans
open Contravariant
open Categoryᴰ
open UniversalElementᴰ
open isIsoOver
private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _ (C : Category ℓC ℓC') (ℓS ℓSᴰ : Level) where
  private
    module 𝓟ᴰ = Categoryᴰ (PRESHEAFᴰ C ℓS ℓSᴰ)
  hasVerticalTerminals : VerticalTerminals (PRESHEAFᴰ C ℓS ℓSᴰ)
  hasVerticalTerminals P .vertexᴰ = ⊤𝓟 (∫ᴾ P) ℓSᴰ .fst
  hasVerticalTerminals P .elementᴰ = tt
  hasVerticalTerminals P .universalᴰ .inv α tt = natTrans (λ x₁ _ → tt*) (λ _ → refl)
  hasVerticalTerminals P .universalᴰ .rightInv _ _ = refl
  hasVerticalTerminals P .universalᴰ .leftInv α αᴰ =
    makeNatTransPathP _ _ refl

  open UniversalElementᵛ
  hasVerticalProducts : VerticalBinProducts (PRESHEAFᴰ C ℓS ℓSᴰ)
  hasVerticalProducts (Pᴰ , Pᴰ') .vertexᵛ = ×𝓟 _ _ Pᴰ Pᴰ' .BinProduct.binProdOb
  hasVerticalProducts (Pᴰ , Pᴰ') .elementᵛ =
    (seqTrans (×𝓟 _ _ Pᴰ Pᴰ' .BinProduct.binProdPr₁) (idTransᴰ _ _ _))
    , (seqTrans (×𝓟 _ _ Pᴰ Pᴰ' .BinProduct.binProdPr₂) (idTransᴰ _ _ _))
  hasVerticalProducts (Pᴰ , Pᴰ') .universalᵛ .fst (id∘αᴰ , id∘αᴰ') = natTrans
    (λ (x , x') q → ((id∘αᴰ ⟦ _ ⟧) q) , (id∘αᴰ' ⟦ _ ⟧) q)
    λ (f , f-comm) → funExt λ q → ΣPathP (funExt⁻ (id∘αᴰ .N-hom _) _ , funExt⁻ (id∘αᴰ' .N-hom _) _)
  hasVerticalProducts (Pᴰ , Pᴰ') .universalᵛ .snd .fst (id∘αᴰ , id∘αᴰ') =
    ΣPathP
     ( makeNatTransPath (sym (transport-filler _ _))
     , makeNatTransPath (sym (transport-filler _ _)))
  -- may god forgive me for this "proof"
  hasVerticalProducts (Pᴰ , Pᴰ') .universalᵛ {y = Q}{yᴰ = Qᴾ}{f = α} .snd .snd αᴰ = makeNatTransPath (funExt λ q → funExt λ q' →
    ΣPathP
    (
      fromPathP
       {A =
        λ i₃ →
          F-ob Pᴰ
          (transp (λ i₁ → ob C) i₃ (q .fst) ,
           N-ob α (transp (λ i₁ → ob C) i₃ (q .fst))
           (transp
            (λ i₄ → fst (F-ob Q (transp (λ i₂ → ob C) (i₃ ∨ ~ i₄) (q .fst))))
            i₃ (q .snd)))
          .fst}
       (λ i → αᴰ .N-ob (transport-filler (λ j → Σ (ob C) (λ c → fst (F-ob Q c))) q (~ i))
                       (transport-filler (λ j → Qᴾ .F-ob (transp (λ j₁ → Σ (ob C) (λ c → fst (F-ob Q c))) (~ j) q) .fst) q' (~ i)) .fst)
    ,
      fromPathP
       {A =
        λ i →
          F-ob Pᴰ'
         (transp (λ i₁ → ob C) i (q .fst) ,
          N-ob α (transp (λ i₁ → ob C) i (q .fst))
          (transp
           (λ i₁ → fst (F-ob Q (transp (λ i₂ → ob C) (i ∨ ~ i₁) (q .fst)))) i
           (q .snd)))
         .fst }
       (λ i → αᴰ .N-ob (transport-filler (λ j → Σ (ob C) (λ c → fst (F-ob Q c))) q (~ i))
                       (transport-filler (λ j → Qᴾ .F-ob (transp (λ j₁ → Σ (ob C) (λ c → fst (F-ob Q c))) (~ j) q) .fst) q' (~ i)) .snd)
