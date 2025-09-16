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
    open LocallyRepresentableⱽNotation Pᴰ _×ⱽ_*Pᴰ

    ⇒PshSmall-app : PshHomⱽ (((Pᴰ , _×ⱽ_*Pᴰ) ⇒PshSmallⱽ Qᴰ) ×ⱽPsh Pᴰ) Qᴰ
    ⇒PshSmall-app .N-obᴰ (α , pᴰ) =
      Qᴰ.reind (P.⋆IdL _) $
        introLR Cᴰ.idᴰ (Pᴰ.reind (sym $ P.⋆IdL _) pᴰ) Qᴰ.⋆ᴰ α 
    ⇒PshSmall-app .N-homᴰ {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {p} {γᴰ} {α , pᴰ} = Qᴰ.rectify $ Qᴰ.≡out $
      sym (Qᴰ.reind-filler _ _)
      ∙ sym (Qᴰ.⋆Assoc _ _ _)
      ∙ Qᴰ.⟨ app-naturality-lemma ⟩⋆⟨⟩
      ∙ Qᴰ.⋆Assoc _ _ _
      ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩
