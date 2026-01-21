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
open import Cubical.Categories.Displayed.Presheaf.Constructions.ReindexFunctor
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.Exponential.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Exponential.UniversalProperty
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable


open Bifunctorᴰ
open Category
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
    -- Some isomorphism principles
    module _ {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
      {F : Functor D C}{Fᴰ : Functorᴰ F Dᴰ Cᴰ}
      (_×ⱽ_*Fᴰ*Pᴰ : LocallyRepresentableⱽ (reindPshᴰFunctor Fᴰ Pᴰ))
      (presLRⱽ : preservesLocalReprⱽ Fᴰ (reindPshᴰFunctor Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*Fᴰ*Pᴰ)
      where
      private
        module D = Category D
        module Dᴰ = Fibers Dᴰ
        module Fᴰ*Qᴰ = PresheafᴰNotation (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
        module Fᴰ*⟨Pᴰ⇒Qᴰ⟩ = PresheafᴰNotation (Pᴰ⇒Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
        Fᴰ*Pᴰ⇒Fᴰ*Qᴰ = (reindPshᴰFunctor Fᴰ Pᴰ , _×ⱽ_*Fᴰ*Pᴰ) ⇒PshSmallⱽ reindPshᴰFunctor Fᴰ Qᴰ
      reindPshᴰFunctor⇒PshSmall : PshIsoⱽ Fᴰ*Pᴰ⇒Fᴰ*Qᴰ (reindPshᴰFunctor Fᴰ Pᴰ⇒Qᴰ)
      reindPshᴰFunctor⇒PshSmall .fst .N-obᴰ {Γ} {Γᴰ} {p} qᴰ⟨Γ,p⟩ =
        UEⱽ-essUniq (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ) (preservesLocalReprⱽ→UEⱽ Fᴰ (reindPshᴰFunctor Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*Fᴰ*Pᴰ presLRⱽ Γᴰ p) .fst
        Qᴰ.⋆ⱽᴰ qᴰ⟨Γ,p⟩
      reindPshᴰFunctor⇒PshSmall .fst .N-homᴰ {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {p} {γᴰ} {qᴰ⟨Γ,p⟩} = Qᴰ.rectify $ Qᴰ.≡out $
        (sym $ Qᴰ.⋆Assocⱽᴰᴰ _ _ _)
        ∙ Qᴰ.⟨ (sym $ Cᴰ.reind-filler _ _) ∙ presLRⱽ-Isoⱽ-natural Fᴰ Pᴰ _×ⱽ_*Fᴰ*Pᴰ _×ⱽ_*Pᴰ presLRⱽ γᴰ p ∙ Cᴰ.reind-filler _ _  ⟩⋆⟨ refl ⟩
        ∙ Qᴰ.⋆Assocᴰⱽᴰ _ _ _
      reindPshᴰFunctor⇒PshSmall .snd {Γ} {Γᴰ} .inv p qᴰ⟨Γ,p⟩ =
        invIsoⱽ _ (UEⱽ-essUniq (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ) (preservesLocalReprⱽ→UEⱽ Fᴰ (reindPshᴰFunctor Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*Fᴰ*Pᴰ presLRⱽ Γᴰ p)) .fst
        Qᴰ.⋆ⱽᴰ qᴰ⟨Γ,p⟩
      reindPshᴰFunctor⇒PshSmall .snd {Γ} {Γᴰ} .rightInv p qᴰ⟨Γ,p⟩ = Qᴰ.rectify $ Qᴰ.≡out $
        sym (Qᴰ.⋆Assocⱽⱽᴰ _ _ _)
        ∙ Qᴰ.⟨  Cᴰ.≡in $ CatIsoⱽ→CatIso Cᴰ (UEⱽ-essUniq (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ) (preservesLocalReprⱽ→UEⱽ Fᴰ (reindPshᴰFunctor Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*Fᴰ*Pᴰ presLRⱽ Γᴰ p)) .snd .isIso.ret ⟩⋆ⱽᴰ⟨ refl ⟩
        ∙ Qᴰ.∫⋆ⱽIdL _
      reindPshᴰFunctor⇒PshSmall .snd {Γ} {Γᴰ} .leftInv p qᴰ⟨Γ,p⟩ = Qᴰ.rectify $ Qᴰ.≡out $
        sym (Qᴰ.⋆Assocⱽⱽᴰ _ _ _)
        ∙ Qᴰ.⟨  Cᴰ.≡in $ CatIsoⱽ→CatIso Cᴰ (UEⱽ-essUniq (Fᴰ .F-obᴰ Γᴰ ×ⱽ p *Pᴰ) (preservesLocalReprⱽ→UEⱽ Fᴰ (reindPshᴰFunctor Fᴰ Pᴰ) Pᴰ idPshHomᴰ _×ⱽ_*Fᴰ*Pᴰ presLRⱽ Γᴰ p)) .snd .isIso.sec ⟩⋆ⱽᴰ⟨ refl ⟩
        ∙ Qᴰ.∫⋆ⱽIdL _
