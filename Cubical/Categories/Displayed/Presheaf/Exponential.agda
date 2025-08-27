{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
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
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Limits.BinProduct

open Bifunctorᴰ
open Functorᴰ
open Functor
open isIsoOver
open PshHomᴰ
private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open UniversalElementⱽ
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _
    ((P , Pᴰ , ueⱽ) :
      Σ[ P ∈ Presheaf C ℓP ]
      Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ]
        ∀ {Γ : C.ob} → (Γᴰ : Cᴰ.ob[ Γ ]) →
        (f : PresheafNotation.p[ P ] Γ) →
        UniversalElementⱽ Cᴰ Γ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo f Pᴰ)
        )
    (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ)
    where
    private
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
      module ∫Qᴰ = PresheafNotation (∫P Qᴰ)
      module _
        {Γ : C.ob} {Γᴰ : Cᴰ.ob[ Γ ]}
        {f : PresheafNotation.p[ P ] Γ}
        where
        よΓᴰ×f*Pᴰ = (Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo f Pᴰ
        module よΓᴰ×f*Pᴰ = PresheafⱽNotation よΓᴰ×f*Pᴰ
        module ∫ueⱽ =
          UniversalElementNotation
            (∫ue (ueⱽ Γᴰ f))

    _⇒Pshⱽ_ : Presheafᴰ P Cᴰ ℓQᴰ
    _⇒Pshⱽ_ .F-obᴰ Γᴰ f = Qᴰ .F-obᴰ (ueⱽ Γᴰ f .vertexⱽ) f
    _⇒Pshⱽ_ .F-homᴰ {x = Γ} {y = Δ} {f = γ}
      {xᴰ = Γᴰ} {yᴰ = Δᴰ} γᴰ f fᴰ =
      introᴰ (ueⱽ Γᴰ f)
        (((ueⱽ Δᴰ (γ P.⋆ f)) .elementⱽ .fst Cᴰ.⋆ⱽᴰ γᴰ) ,
          (Pᴰ.reind (P.⋆IdL _) $ ueⱽ Δᴰ (γ P.⋆ f) .elementⱽ .snd))
      Qᴰ.⋆ᴰ fᴰ
    _⇒Pshⱽ_ .F-idᴰ {x = Γ}{xᴰ = Γᴰ} =
        {!!}
        -- funExt₂ λ f fᴰ →
        -- Can't use Qᴰ.rectify because
        -- of a metavariable issue

        --   (Qᴰ.rectify $ Qᴰ.≡out $
        --     {!!}
        --     ∙ ΣPathP (
        --         funExt⁻ (sym $ P .F-id) f ,
        --         {!subst-filler
        --           (λ z → ⟨ Qᴰ .F-obᴰ (ueⱽ Γᴰ ? .vertexⱽ) ? ⟩)
        --           ?
        --           ?
        --           !})
        --   )
        --   ◁
        --   (symP $ subst-filler
        --     (λ z → ⟨ Qᴰ .F-obᴰ (ueⱽ Γᴰ z .vertexⱽ) z ⟩)
        --     (funExt⁻ (sym $ P .F-id) f)
        --     fᴰ
        --     )
    _⇒Pshⱽ_ .F-seqᴰ = {!!}

  Exponentialⱽ : ∀ {c} → (cᴰ cᴰ' : Cᴰ.ob[ c ]) →
    -- this repr assumption can be simplified with BinProductsⱽ
    (repr : ∀ {d} dᴰ (f : C [ d , c ]) →
      UniversalElementⱽ Cᴰ d
        ((Cᴰ [-][-, dᴰ ]) ×ⱽPsh reindYo f (Cᴰ [-][-, cᴰ ]))) →
    Type _
  Exponentialⱽ {c} cᴰ cᴰ' repr =
    UniversalElementⱽ Cᴰ c
      ((_ , (Cᴰ [-][-, cᴰ ]) , repr) ⇒Pshⱽ (Cᴰ [-][-, cᴰ' ]))
