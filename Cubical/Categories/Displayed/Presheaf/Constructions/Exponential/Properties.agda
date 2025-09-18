{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Exponential.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws hiding (cong₂Funct)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.More

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory using (∫C)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.Exponential.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable


open Bifunctorᴰ
open Functor
open Functorᴰ
open isIsoOver
open PshHom
open PshIso
open PshHomᴰ

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ {P : Presheaf C ℓP}
    ((Pᴰ , _×ⱽ_*Pᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableⱽ Pᴰ)
    (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ)
    where
    open UniversalElementⱽ
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      Pᴰ⇒Qᴰ = (Pᴰ , _×ⱽ_*Pᴰ) ⇒PshSmallⱽ Qᴰ
      module Pᴰ⇒Qᴰ = PresheafᴰNotation Pᴰ⇒Qᴰ
    -- Firstly, the universal property of ⇒PshSmall
    module _ where
      open LocallyRepresentableⱽNotation Pᴰ _×ⱽ_*Pᴰ

      ⇒PshSmallⱽ-app : PshHomⱽ (Pᴰ⇒Qᴰ ×ⱽPsh Pᴰ) Qᴰ
      ⇒PshSmallⱽ-app .N-obᴰ (α , pᴰ) =
        Qᴰ.reind (P.⋆IdL _) $
          introLR Cᴰ.idᴰ (Pᴰ.reind (sym $ P.⋆IdL _) pᴰ) Qᴰ.⋆ᴰ α
      ⇒PshSmallⱽ-app .N-homᴰ {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {p} {γᴰ} {α , pᴰ} = Qᴰ.rectify $ Qᴰ.≡out $
        sym (Qᴰ.reind-filler _ _)
        ∙ sym (Qᴰ.⋆Assoc _ _ _)
        ∙ Qᴰ.⟨ app-naturality-lemma ⟩⋆⟨⟩
        ∙ Qᴰ.⋆Assoc _ _ _
        ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩
    module _ {R : Presheaf C ℓR}{Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}{α : PshHom R P} where
      private
        module Rᴰ = PresheafᴰNotation Rᴰ
      open LocallyRepresentableⱽNotation _ _×ⱽ_*Pᴰ
      ⇒PshSmallⱽ-introᴰ :
        PshHomᴰ α (Rᴰ ×ⱽPsh reind α Pᴰ) Qᴰ
        → PshHomᴰ α Rᴰ Pᴰ⇒Qᴰ
      ⇒PshSmallⱽ-introᴰ αᴰ⟨rᴰ,pᴰ⟨α⟩⟩ .N-obᴰ {Γ} {Γᴰ} {r} rᴰ =
        αᴰ⟨rᴰ,pᴰ⟨α⟩⟩ .N-obᴰ ((π₁LR Γᴰ (α .N-ob Γ r) Rᴰ.⋆ⱽᴰ rᴰ) , (Pᴰ.reind (P.⋆IdL _) (π₂LR Γᴰ (α .N-ob Γ r))))
      ⇒PshSmallⱽ-introᴰ αᴰ⟨rᴰ,pᴰ⟨α⟩⟩ .N-homᴰ {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {r} {γᴰ} {rᴰ} =
        rectify {!!}
        (compPathP (λ i → αᴰ⟨rᴰ,pᴰ⟨α⟩⟩ .N-obᴰ ({!!} , {!!})) (αᴰ⟨rᴰ,pᴰ⟨α⟩⟩ .N-homᴰ))
        where
          module αᴰ⟨rᴰ,pᴰ⟨α⟩⟩ = PshHomᴰ αᴰ⟨rᴰ,pᴰ⟨α⟩⟩
          -- lem1 :
          --   PathP (λ i → ?)
          --     (π₁LR Δᴰ (α .N-ob Δ ((R PresheafNotation.⋆ γ) r)) Rᴰ.⋆ⱽᴰ (γᴰ Rᴰ.⋆ᴰ rᴰ))
          --        ≡ (F-homᴰ Rᴰ (funcLR γᴰ) r (π₁LR Γᴰ (α .N-ob Γ r) Rᴰ.⋆ⱽᴰ rᴰ))
          -- lem1 = ?
          -- lem2 : 
      -- ((π₁LR Δᴰ (α .N-ob Δ ((R PresheafNotation.⋆ γ) r)) Rᴰ.⋆ⱽᴰ
      --   (γᴰ Rᴰ.⋆ᴰ rᴰ))
      --  ,
      --  Pᴰ.reind (P.⋆IdL (α .N-ob Δ ((R PresheafNotation.⋆ γ) r)))
      --  (π₂LR Δᴰ (α .N-ob Δ ((R PresheafNotation.⋆ γ) r))))
      --  ≡
      -- γᴰ Pᴰ⇒Qᴰ.⋆ᴰ
      -- αᴰ⟨rᴰ,pᴰ⟨α⟩⟩.N-obᴰ
      -- ((π₁LR Γᴰ (α .N-ob Γ r) Rᴰ.⋆ⱽᴰ rᴰ) ,
      --  Pᴰ.reind (P.⋆IdL (α .N-ob Γ r)) (π₂LR Γᴰ (α .N-ob Γ r)))
       
          -- lem : ((π₁LR Γᴰ (α .N-ob Γ r) Rᴰ.⋆ⱽᴰ rᴰ) , (Pᴰ.reind (P.⋆IdL _) (π₂LR Γᴰ (α .N-ob Γ r))))
    module _ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ} where
      private
        module Rᴰ = PresheafᴰNotation Rᴰ
      open LocallyRepresentableⱽNotation _ _×ⱽ_*Pᴰ
      ⇒PshSmallⱽ-introⱽ :
        PshHomⱽ (Rᴰ ×ⱽPsh Pᴰ) Qᴰ
        → PshHomⱽ Rᴰ Pᴰ⇒Qᴰ
      ⇒PshSmallⱽ-introⱽ α⟨rᴰ,pᴰ⟩ =
        ⇒PshSmallⱽ-introᴰ ((idPshHomᴰ ×ⱽHom invPshIsoⱽ (reind-idIsoⱽ Pᴰ) .fst) ⋆PshHomⱽ α⟨rᴰ,pᴰ⟩)
    -- Some isomorphism principles
    module _ {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
      {F : Functor D C}{Fᴰ : Functorᴰ F Dᴰ Cᴰ}
      (_×ⱽ_*Fᴰ*Pᴰ : LocallyRepresentableⱽ (reindFunc' Fᴰ Pᴰ))
      (presLRⱽ : preservesLocalReprⱽ Fᴰ (reindFunc' Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*Fᴰ*Pᴰ)
      where
      private
        module D = Category D
        module Dᴰ = Fibers Dᴰ
        module Fᴰ*Qᴰ = PresheafᴰNotation (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
        module Fᴰ*⟨Pᴰ⇒Qᴰ⟩ = PresheafᴰNotation (Pᴰ⇒Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
        Fᴰ*Pᴰ⇒Fᴰ*Qᴰ = (reindFunc' Fᴰ Pᴰ , _×ⱽ_*Fᴰ*Pᴰ) ⇒PshSmallⱽ reindFunc' Fᴰ Qᴰ
      reindFunc⇒PshSmall : PshIsoⱽ Fᴰ*Pᴰ⇒Fᴰ*Qᴰ (reindFunc' Fᴰ Pᴰ⇒Qᴰ)
      reindFunc⇒PshSmall .fst .N-obᴰ {Γ} {Γᴰ} {p} qᴰ⟨Γ,p⟩ =
        UEⱽ-essUniq (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ) (preservesLocalReprⱽ→UEⱽ Fᴰ (reindFunc' Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*Fᴰ*Pᴰ presLRⱽ Γᴰ p) .fst
        Qᴰ.⋆ⱽᴰ qᴰ⟨Γ,p⟩
      reindFunc⇒PshSmall .fst .N-homᴰ {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {p} {γᴰ} {qᴰ⟨Γ,p⟩} = Qᴰ.rectify $ Qᴰ.≡out $
        (sym $ Qᴰ.⋆Assocⱽᴰᴰ _ _ _)
        ∙ Qᴰ.⟨ (sym $ Cᴰ.reind-filler _ _) ∙ presLRⱽ-Isoⱽ-natural Fᴰ Pᴰ _×ⱽ_*Fᴰ*Pᴰ _×ⱽ_*Pᴰ presLRⱽ γᴰ p ∙ Cᴰ.reind-filler _ _  ⟩⋆⟨ refl ⟩
        ∙ Qᴰ.⋆Assocᴰⱽᴰ _ _ _
      reindFunc⇒PshSmall .snd {Γ} {Γᴰ} .inv p qᴰ⟨Γ,p⟩ =
        invIsoⱽ _ (UEⱽ-essUniq (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ) (preservesLocalReprⱽ→UEⱽ Fᴰ (reindFunc' Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*Fᴰ*Pᴰ presLRⱽ Γᴰ p)) .fst
        Qᴰ.⋆ⱽᴰ qᴰ⟨Γ,p⟩
      reindFunc⇒PshSmall .snd {Γ} {Γᴰ} .rightInv p qᴰ⟨Γ,p⟩ = Qᴰ.rectify $ Qᴰ.≡out $
        sym (Qᴰ.⋆Assocⱽⱽᴰ _ _ _)
        ∙ Qᴰ.⟨  Cᴰ.≡in $ CatIsoⱽ→CatIso Cᴰ (UEⱽ-essUniq (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ) (preservesLocalReprⱽ→UEⱽ Fᴰ (reindFunc' Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*Fᴰ*Pᴰ presLRⱽ Γᴰ p)) .snd .isIso.ret ⟩⋆ⱽᴰ⟨ refl ⟩
        ∙ Qᴰ.∫⋆ⱽIdL _
      reindFunc⇒PshSmall .snd {Γ} {Γᴰ} .leftInv p qᴰ⟨Γ,p⟩ = Qᴰ.rectify $ Qᴰ.≡out $
        sym (Qᴰ.⋆Assocⱽⱽᴰ _ _ _)
        ∙ Qᴰ.⟨  Cᴰ.≡in $ CatIsoⱽ→CatIso Cᴰ (UEⱽ-essUniq (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ) (preservesLocalReprⱽ→UEⱽ Fᴰ (reindFunc' Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*Fᴰ*Pᴰ presLRⱽ Γᴰ p)) .snd .isIso.sec ⟩⋆ⱽᴰ⟨ refl ⟩
        ∙ Qᴰ.∫⋆ⱽIdL _

-- Derived Combinators
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  
  module _
    {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : LocallyRepresentableⱽPresheafᴰ P Cᴰ ℓPᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    (α : PshHom Q P)
    where
    reind⇒PshSmallⱽ :
      PshIsoⱽ (reindLocallyRepresentableⱽPresheafᴰ α Pᴰ ⇒PshSmallⱽ reind α Pᴰ') (reind α (Pᴰ ⇒PshSmallⱽ Pᴰ'))
    reind⇒PshSmallⱽ .fst = reind-introⱽ (⇒PshSmallⱽ-introᴰ Pᴰ Pᴰ' (⇒PshSmallⱽ-app _ _ ⋆PshHomⱽᴰ reind-π))
    reind⇒PshSmallⱽ .snd .inv _ = reind⇒PshSmallⱽ⁻ .N-obᴰ where
      reind⇒PshSmallⱽ⁻ :
        PshHomⱽ (reind α (Pᴰ ⇒PshSmallⱽ Pᴰ')) (reindLocallyRepresentableⱽPresheafᴰ α Pᴰ ⇒PshSmallⱽ reind α Pᴰ')
      reind⇒PshSmallⱽ⁻ = ⇒PshSmallⱽ-introⱽ _ _ (invPshIsoⱽ reind×ⱽIsoⱽ .fst ⋆PshHomⱽ reindPshHomⱽ (⇒PshSmallⱽ-app Pᴰ Pᴰ'))
    -- do not implement manually
    reind⇒PshSmallⱽ .snd .rightInv = {!!}
    reind⇒PshSmallⱽ .snd .leftInv = {!!}
    -- reind⇒PshSmall .fst = reind-introⱽ (⇒PshSmall-introᴰ ({!⇒PshSmall-app!} ⋆PshHomⱽᴰ reind-π))
    -- reind⇒PshSmall .snd .inv = λ a → reind⇒PshSmall⁻ .N-obᴰ where
    --   reind⇒PshSmall⁻ : PshHomⱽ (reind α Pᴰ⇒Qᴰ) ((reind α Pᴰ , reindLocallyRepresentableⱽ α Pᴰ _×ⱽ_*Pᴰ) ⇒PshSmallⱽ reind α Qᴰ)
    --   reind⇒PshSmall⁻ = {!⇒PshSmall-introⱽ!}
    -- reind⇒PshSmall .snd .rightInv = {!!}
    -- reind⇒PshSmall .snd .leftInv = {!!}

  module _
    {P : Presheaf C ℓP}
    {Pᴰ : LocallyRepresentableⱽPresheafᴰ P Cᴰ ℓPᴰ}
    {Qᴰ : LocallyRepresentableⱽPresheafᴰ P Cᴰ ℓQᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    {Qᴰ' : Presheafᴰ P Cᴰ ℓQᴰ'}
    where
      _⇒ⱽHomⱽ_
        : PshHomⱽ (Qᴰ .fst) (Pᴰ .fst)
        → PshHomⱽ Pᴰ' Qᴰ'
        → PshHomⱽ (Pᴰ ⇒PshSmallⱽ Pᴰ') (Qᴰ ⇒PshSmallⱽ Qᴰ')
      αᴰ ⇒ⱽHomⱽ βᴰ = ⇒PshSmallⱽ-introⱽ Qᴰ Qᴰ'
        ((idPshHomᴰ ×ⱽHom αᴰ) ⋆PshHomⱽ ⇒PshSmallⱽ-app Pᴰ Pᴰ' ⋆PshHomⱽ βᴰ)
  module _
    {P : Presheaf C ℓP}
    {Pᴰ : LocallyRepresentableⱽPresheafᴰ P Cᴰ ℓPᴰ}
    {Qᴰ : LocallyRepresentableⱽPresheafᴰ P Cᴰ ℓQᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    {Qᴰ' : Presheafᴰ P Cᴰ ℓQᴰ'}
    where
      _⇒ⱽIsoⱽ_
        : PshIsoⱽ (Pᴰ .fst) (Qᴰ .fst)
        → PshIsoⱽ Pᴰ' Qᴰ'
        → PshIsoⱽ (Pᴰ ⇒PshSmallⱽ Pᴰ') (Qᴰ ⇒PshSmallⱽ Qᴰ')
      (αⱽ ⇒ⱽIsoⱽ βⱽ) .fst = invPshIsoⱽ αⱽ .fst ⇒ⱽHomⱽ βⱽ .fst
      (αⱽ ⇒ⱽIsoⱽ βⱽ) .snd .inv = λ _ → (αⱽ .fst ⇒ⱽHomⱽ invPshIsoⱽ βⱽ .fst) .N-obᴰ
      (αⱽ ⇒ⱽIsoⱽ βⱽ) .snd .rightInv = {!!}
      (αⱽ ⇒ⱽIsoⱽ βⱽ) .snd .leftInv = {!!}
