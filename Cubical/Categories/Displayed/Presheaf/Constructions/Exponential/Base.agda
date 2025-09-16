{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Exponential.Base where

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

  module _ {(P , _×P) : Σ[ P ∈ Presheaf C ℓP ] ∀ c → UniversalElement C ((C [-, c ]) ×Psh P)}
           {Q : Presheaf C ℓQ}
           ((Pᴰ , _×ᴰPᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableᴰ (P , _×P) Pᴰ)
           (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
           where
    open UniversalElement
    open UniversalElementᴰ
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      ∫⇒Small = (_ , (∫LocallyRepresentable ((Pᴰ , _×ᴰPᴰ)))) ⇒PshSmall ∫P Qᴰ
      module ∫⇒Small = PresheafNotation ∫⇒Small
    _⇒PshSmallᴰ_ : Presheafᴰ ((P , _×P) ⇒PshSmall Q) Cᴰ ℓQᴰ
    _⇒PshSmallᴰ_ .F-obᴰ {Γ} Γᴰ = Qᴰ .F-obᴰ ((Γᴰ ×ᴰPᴰ) .vertexᴰ)
    _⇒PshSmallᴰ_ .F-homᴰ {Γ} {Δ} {γ} {Γᴰ} {Δᴰ} γᴰ q qᴰ =
      ((γ , γᴰ) ∫⇒Small.⋆ (q , qᴰ)) .snd
    _⇒PshSmallᴰ_ .F-idᴰ {Γ} {Γᴰ} = funExt λ q → funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      funExt⁻ (∫⇒Small .F-id) (q , qᴰ)
    _⇒PshSmallᴰ_ .F-seqᴰ γᴰ δᴰ = funExt λ q → funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
      funExt⁻ (∫⇒Small .F-seq (_ , γᴰ) (_ , δᴰ)) (q , qᴰ)

  module _ {P : Presheaf C ℓP}
    ((Pᴰ , _×ⱽ_*Pᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableⱽ Pᴰ)
    (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ)
    where
    open UniversalElementⱽ
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
    open LocallyRepresentableⱽNotation Pᴰ _×ⱽ_*Pᴰ
    -- Γᴰ ⊢ (Pᴰ ⇒ Qᴰ)(p) := Γᴰ , Pᴰ(p) ⊢ Qᴰ(p)
    _⇒PshSmallⱽ_ : Presheafᴰ P Cᴰ ℓQᴰ
    _⇒PshSmallⱽ_ .F-obᴰ {Γ} Γᴰ p = Qᴰ .F-obᴰ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ p
    _⇒PshSmallⱽ_ .F-homᴰ {Γ} {Δ} {γ} {Γᴰ} {Δᴰ} γᴰ p qᴰ =
      funcLR γᴰ Qᴰ.⋆ᴰ qᴰ
    _⇒PshSmallⱽ_ .F-idᴰ {Γ}{Γᴰ} = funExt λ p → funExt λ qᴰ →
      rectify
        (sym (congS₂Bifunct Qᴰ~ _ _ _ _) ∙ congS₂ (congS₂ Qᴰ~) (P.isSetPsh _ _ _ _) (P.isSetPsh _ _ _ _))
        $ compPathP
          (λ i → funcLR-id i Qᴰ.⋆ᴰ qᴰ)
          (Qᴰ.≡out $ Qᴰ.⋆IdL _)
      where
        Qᴰ~ : (p p' : P.p[ Γ ]) → Type _
        Qᴰ~ p' p = Qᴰ.p[ p ][ ⌈ Γᴰ ×ⱽ p' *Pᴰ⌉ ]
    _⇒PshSmallⱽ_ .F-seqᴰ {Γ} {Δ} {Θ} {γ} {δ} {Γᴰ} {Δᴰ} {Θᴰ} γᴰ δᴰ = funExt λ p → funExt λ qᴰ →
      rectify
        (sym (congS₂Bifunct Qᴰ~ _ _ _ _) ∙ congS₂ (congS₂ Qᴰ~) (P.isSetPsh _ _ _ _) (P.isSetPsh _ _ _ _))
        $ compPathP (λ i → funcLR-seq γᴰ δᴰ i Qᴰ.⋆ᴰ qᴰ) (Qᴰ.≡out $ Qᴰ.⋆Assoc _ _ _)
      where
        Qᴰ~ : (p p' : P.p[ Θ ]) → Type _
        Qᴰ~ p p' = Qᴰ.p[ p ][ ⌈ Θᴰ ×ⱽ p' *Pᴰ⌉ ]
