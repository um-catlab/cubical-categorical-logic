{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf.CCC

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Presheaf using (UniversalElementᴰ)
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Base

open Category
open Functor
open NatTrans
open Contravariant
open Categoryᴰ
open UniversalElementᴰ
open CartesianOver

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

module _ (C : Category ℓC ℓC') (ℓS ℓSᴰ : Level) where
  PRESHEAFᴰ-VerticalTerminals : VerticalTerminals (PRESHEAFᴰ C ℓS ℓSᴰ)
  PRESHEAFᴰ-VerticalTerminals P .vertexᴰ = ⊤𝓟 _ _ .fst
  PRESHEAFᴰ-VerticalTerminals P .elementᴰ = tt
  PRESHEAFᴰ-VerticalTerminals P .universalᴰ .equiv-proof _ = uniqueExists
    (natTrans (λ _ _ → tt*) (λ _ → funExt (λ _ → refl)))
    (isPropUnit _ _)
    (λ _ → isSetUnit _ _)
    (λ _ _ → makeNatTransPath (funExt (λ _ → funExt (λ _ → isPropUnit* _ _))))

  private
    -- present PRESHEAFᴰ-VerticalProducts in a more implementation agnostic way
    module M {P : Presheaf C ℓS} (Pᴰ Pᴰ' : Presheafᴰ C ℓS ℓSᴰ P) where
      vprod : Presheafᴰ C _ _ P
      vprod = ×𝓟 _ _ Pᴰ Pᴰ' .BinProduct.binProdOb

      π₁ : NatTransᴰ C _ _ (idTrans P) vprod Pᴰ
      π₁ = seqTrans (×𝓟 _ _ Pᴰ Pᴰ' .BinProduct.binProdPr₁) (idTransᴰ _ _ _)

      π₂ : NatTransᴰ C _ _ (idTrans P) vprod Pᴰ'
      π₂ = seqTrans (×𝓟 _ _ Pᴰ Pᴰ' .BinProduct.binProdPr₂) (idTransᴰ _ _ _)

      module _ {Q}{Qᴰ : Presheafᴰ C _ _ Q}{α : Q ⇒ P}
        (id∘αᴰ : NatTransᴰ C _ _ (seqTrans α (idTrans P)) Qᴰ Pᴰ)
        (id∘αᴰ' : NatTransᴰ C _ _ (seqTrans α (idTrans P)) Qᴰ Pᴰ') where
        pair : NatTransᴰ C _ _ α Qᴰ vprod
        pair = natTrans
          (λ (Γ , ϕ) ϕᴰ → (id∘αᴰ ⟦ Γ , ϕ ⟧) ϕᴰ , (id∘αᴰ' ⟦ Γ , ϕ ⟧) ϕᴰ)
          (λ {x = Γ,ϕ}{y = Δ,ψ} (f , p) → funExt (λ ϕᴰ → ≡-×
            (funExt⁻ (id∘αᴰ .N-hom (f , p)) ϕᴰ ∙
              congS (λ x → (Pᴰ ⟪ _ , x ⟫) ((id∘αᴰ ⟦ Γ,ϕ ⟧) ϕᴰ))
              ((P ⟅ _ ⟆) .snd _ _ _ _))
            (funExt⁻ (id∘αᴰ' .N-hom (f , p)) ϕᴰ ∙
              congS (λ x → (Pᴰ' ⟪ _ , x ⟫) ((id∘αᴰ' ⟦ Γ,ϕ ⟧) ϕᴰ))
              ((P ⟅ _ ⟆) .snd _ _ _ _))))
        module _
          (pair' : NatTransᴰ C _ _ α Qᴰ vprod)
          (pair'-ob : pair' ⟦_⟧ ≡ pair ⟦_⟧) where
          module _
            (π₁' : NatTransᴰ C _ _ (idTrans P) vprod Pᴰ)
            (π₁'-ob : π₁' ⟦_⟧ ≡ π₁ ⟦_⟧) where
            β₁ : seqTransᴰ C _ _ pair' π₁' ≡ id∘αᴰ
            β₁ = makeNatTransPath (funExt (λ _ → funExt (λ _ →
              funExt⁻ (funExt⁻ π₁'-ob (_ , (α ⟦ _ ⟧) _)) ((pair' ⟦ _ ⟧) _) ∙
              congS fst (funExt⁻ (funExt⁻ pair'-ob _) _))))
          module _
            (π₂' : NatTransᴰ C _ _ (idTrans P) vprod Pᴰ')
            (π₂'-ob : π₂' ⟦_⟧ ≡ π₂ ⟦_⟧) where
            β₂ : seqTransᴰ C _ _ pair' π₂' ≡ id∘αᴰ'
            β₂ = makeNatTransPath (funExt (λ _ → funExt (λ _ →
              funExt⁻ (funExt⁻ π₂'-ob (_ , (α ⟦ _ ⟧) _)) ((pair' ⟦ _ ⟧) _) ∙
              congS snd (funExt⁻ (funExt⁻ pair'-ob _) _))))

  PRESHEAFᴰ-VerticalProducts : VerticalBinProducts (PRESHEAFᴰ C ℓS ℓSᴰ)
  PRESHEAFᴰ-VerticalProducts (Pᴰ , Pᴰ') .vertexᴰ = M.vprod Pᴰ Pᴰ'
  PRESHEAFᴰ-VerticalProducts (Pᴰ , Pᴰ') .elementᴰ = M.π₁ Pᴰ Pᴰ' , M.π₂ Pᴰ Pᴰ'
  PRESHEAFᴰ-VerticalProducts (Pᴰ , Pᴰ') .universalᴰ
    .equiv-proof (id∘αᴰ , id∘αᴰ') = uniqueExists
    pair
    (≡-×
      (N.β₁ id∘αᴰ id∘αᴰ' pair refl (M.π₁ _ _) refl)
      (N.β₂ id∘αᴰ id∘αᴰ' pair refl (M.π₂ _ _) refl))
    (λ pair' → isSet× isSetNatTrans isSetNatTrans
      (seqTransᴰ C _ _ pair'
        (PRESHEAFᴰ-VerticalProducts (Pᴰ , Pᴰ') .elementᴰ .fst) ,
      seqTransᴰ C _ _ pair'
        (PRESHEAFᴰ-VerticalProducts (Pᴰ , Pᴰ') .elementᴰ .snd))
      (id∘αᴰ , id∘αᴰ'))
    λ _ p → makeNatTransPath (funExt (λ _ → funExt (λ _ → ≡-×
      (funExt⁻ (funExt⁻ (sym (congS (N-ob ∘S fst) p)) _) _)
      (funExt⁻ (funExt⁻ (sym (congS (N-ob ∘S snd) p)) _) _))))
    where
    module N = M Pᴰ Pᴰ'
    pair = N.pair id∘αᴰ id∘αᴰ'

  PRESHEAFᴰ-isFibration : isFibration (PRESHEAFᴰ C ℓS ℓSᴰ)
  PRESHEAFᴰ-isFibration {d = Q} (P , Pᴰ , α) = CartesianOver→CartesianLift
    (PRESHEAFᴰ C _ _)
    co
    where
    co : CartesianOver (PRESHEAFᴰ C _ _) Pᴰ α
    co .f*cᴰ' .F-ob (Γ , ϕ) = Pᴰ ⟅ Γ , (α ⟦ Γ ⟧) ϕ ⟆
    co .f*cᴰ' .F-hom {x = Γ,ϕ} {y = Δ,ψ} (f , p) = Pᴰ ⟪ f ,
      sym (funExt⁻ (α .N-hom f) (Γ,ϕ .snd)) ∙
      congS (α ⟦ Δ,ψ .fst ⟧) p ⟫
    co .f*cᴰ' .F-id {x = Γ , ϕ} = funExt (λ α⟦Γ⟧ϕᴰ →
      congS (λ x → (Pᴰ ⟪ C .id , x ⟫) α⟦Γ⟧ϕᴰ) ((P ⟅ _ ⟆) .snd _ _ _ _) ∙
      funExt⁻ (Pᴰ .F-id) α⟦Γ⟧ϕᴰ)
    co .f*cᴰ' .F-seq (f , p) (g , q) =
      congS (λ x → Pᴰ ⟪ _ , x ⟫) ((P ⟅ _ ⟆) .snd _ _ _ _) ∙
      Pᴰ .F-seq _ _
    co .π = natTrans (λ _ → idfun _) (λ _ → refl)
    co .isCartesian {c'' = R} Rᴰ β βαᴰ = uniqueExists
      (natTrans (βαᴰ ⟦_⟧) (λ _ → funExt (λ ϕᴰ →
        funExt⁻ (βαᴰ .N-hom _) ϕᴰ ∙
        congS (λ x → (Pᴰ ⟪ _ , x ⟫) ((βαᴰ ⟦ _ ⟧) ϕᴰ))
          ((P ⟅ _ ⟆) .snd _ _ _ _))))
      (makeNatTransPath refl)
      (λ _ → isSetNatTrans _ _)
      (λ _ p → makeNatTransPath (sym (congS N-ob p)))
