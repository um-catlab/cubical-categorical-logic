{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.IsoFib where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Profunctor

open Functor
open Functorᴰ

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

module _ {C : Category ℓC ℓC'}{P : Presheaf C ℓP}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ

  module _
    (Qᴰp[_][_] : ∀ {Γ} (p : P.p[ Γ ]) (Γᴰ : Cᴰ.ob[ Γ ]) → Type ℓQᴰ)
    (_Qᴰ⋆ᴰ_ : ∀ {Δ Γ}{Δᴰ Γᴰ}{γ : C [ Δ , Γ ]}{p}
      (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])(s : Qᴰp[ p ][ Γᴰ ])
      → Qᴰp[ γ P.⋆ p ][ Δᴰ ])
    (Pᴰ≅Qᴰ : ∀ {Γ}(p : P.p[ Γ ]) (Γᴰ : Cᴰ.ob[ Γ ])
      → Iso Pᴰ.p[ p ][ Γᴰ ] Qᴰp[ p ][ Γᴰ ])
    (Pᴰ≅Qᴰ-Nhomⱽ : ∀ {Δ Γ}{Δᴰ Γᴰ}{γ : C [ Δ , Γ ]}{p}
      (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])(pᴰ : Pᴰ.p[ p ][ Γᴰ ])
      → (Pᴰ≅Qᴰ (γ P.⋆ p) Δᴰ .Iso.fun $ (γᴰ Pᴰ.⋆ᴰ pᴰ))
        ≡ (γᴰ Qᴰ⋆ᴰ Pᴰ≅Qᴰ p Γᴰ .Iso.fun pᴰ))
    where

    private
      module Qᴰ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]} = hSetReasoning (P .F-ob Γ) (Qᴰp[_][ Γᴰ ])

      opaque
        Pᴰ≅Qᴰ-Nhomⱽ' : ∀ {Δ Γ}{Δᴰ Γᴰ}{γ : C [ Δ , Γ ]}{p}
          (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])(qᴰ : Qᴰp[ p ][ Γᴰ ])
          → (Pᴰ≅Qᴰ (P .F-hom γ p) Δᴰ .Iso.fun $ (γᴰ Pᴰ.⋆ᴰ Pᴰ≅Qᴰ _ _ .Iso.inv qᴰ))
            ≡ (γᴰ Qᴰ⋆ᴰ qᴰ)
        Pᴰ≅Qᴰ-Nhomⱽ' γᴰ qᴰ = Pᴰ≅Qᴰ-Nhomⱽ _ _
          ∙ cong (γᴰ Qᴰ⋆ᴰ_) (Iso.rightInv (Pᴰ≅Qᴰ _ _) qᴰ)

        pushⱽPshᴰ-F-idᴰ : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ])
          → PathP (λ i → (p : fst (P .F-ob Γ)) → Qᴰp[ p ][ Γᴰ ] → Qᴰp[ P .F-id i p ][ Γᴰ ])
              (λ p qᴰ → Cᴰ.idᴰ Qᴰ⋆ᴰ qᴰ)
              (λ p qᴰ → qᴰ)
        pushⱽPshᴰ-F-idᴰ Γᴰ = funExt λ p → funExt λ qᴰ →
          (sym $ Pᴰ≅Qᴰ-Nhomⱽ' Cᴰ.idᴰ qᴰ)
          ◁ (λ i →
            Iso.fun (Pᴰ≅Qᴰ (P .F-id i p) Γᴰ)
              (Pᴰ.⋆IdLᴰ (Iso.inv (Pᴰ≅Qᴰ p Γᴰ) qᴰ) i))
          ▷ Pᴰ≅Qᴰ _ _ .Iso.rightInv _

        pushⱽPshᴰ-F-seqᴰ : ∀ {Θ Δ Γ}{Θᴰ Δᴰ Γᴰ}
          {δ : C [ Θ , Δ ]}
          {γ : C [ Δ , Γ ]}
          (δᴰ : Cᴰ [ δ ][ Θᴰ , Δᴰ ])
          (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
          → PathP
             (λ i →
                (p : P.p[ Γ ]) (qᴰ : Qᴰp[ p ][ Γᴰ ]) → Qᴰp[ P .F-seq γ δ i p ][ Θᴰ ])
             (λ p qᴰ → (δᴰ Cᴰ.⋆ᴰ γᴰ) Qᴰ⋆ᴰ qᴰ)
             λ p qᴰ → δᴰ Qᴰ⋆ᴰ (γᴰ Qᴰ⋆ᴰ qᴰ)
        pushⱽPshᴰ-F-seqᴰ {Θ} {Δ} {Γ} {Θᴰ} {Δᴰ} {Γᴰ} {δ} {γ} δᴰ γᴰ = funExt λ p → funExt λ qᴰ →
          (sym $ Pᴰ≅Qᴰ-Nhomⱽ' (δᴰ Cᴰ.⋆ᴰ γᴰ) qᴰ)
          ◁ (λ i → Iso.fun (Pᴰ≅Qᴰ (P.⋆Assoc δ γ p i) Θᴰ) (Pᴰ.⋆Assocᴰ δᴰ γᴰ (Iso.inv (Pᴰ≅Qᴰ p Γᴰ) qᴰ) i))
          ▷ (cong (Iso.fun (Pᴰ≅Qᴰ (P .F-hom δ (P .F-hom γ p)) Θᴰ)) $ cong (δᴰ Pᴰ.⋆ᴰ_) $
              sym $ Pᴰ≅Qᴰ _ _ .Iso.leftInv _)
          ∙ Pᴰ≅Qᴰ-Nhomⱽ' δᴰ _
          ∙ cong (δᴰ Qᴰ⋆ᴰ_) (Pᴰ≅Qᴰ-Nhomⱽ' γᴰ qᴰ)

    pushⱽPshᴰ : Presheafᴰ P Cᴰ ℓQᴰ
    pushⱽPshᴰ .F-obᴰ Γᴰ p .fst = Qᴰp[ p ][ Γᴰ ]
    pushⱽPshᴰ .F-obᴰ Γᴰ p .snd =
      isOfHLevelRetractFromIso 2 (invIso $ Pᴰ≅Qᴰ p Γᴰ) Pᴰ.isSetPshᴰ
    pushⱽPshᴰ .F-homᴰ γᴰ p pᴰ = γᴰ Qᴰ⋆ᴰ pᴰ
    pushⱽPshᴰ .F-idᴰ {Γ} {Γᴰ} = pushⱽPshᴰ-F-idᴰ Γᴰ
    pushⱽPshᴰ .F-seqᴰ γᴰ δᴰ = pushⱽPshᴰ-F-seqᴰ δᴰ γᴰ

    pushⱽPshᴰ-Isoⱽ : PshIsoⱽ Pᴰ pushⱽPshᴰ
    pushⱽPshᴰ-Isoⱽ .fst .PshHomᴰ.N-obᴰ = Pᴰ≅Qᴰ _ _ .Iso.fun
    pushⱽPshᴰ-Isoⱽ .fst .PshHomᴰ.N-homᴰ = Pᴰ≅Qᴰ-Nhomⱽ _ _
    pushⱽPshᴰ-Isoⱽ .snd .isIsoOver.inv p qᴰ = Pᴰ≅Qᴰ _ _ .Iso.inv qᴰ
    pushⱽPshᴰ-Isoⱽ .snd .isIsoOver.rightInv p qᴰ = Iso.rightInv (Pᴰ≅Qᴰ p _) qᴰ
    pushⱽPshᴰ-Isoⱽ .snd .isIsoOver.leftInv p pᴰ = Iso.leftInv (Pᴰ≅Qᴰ p _) pᴰ

