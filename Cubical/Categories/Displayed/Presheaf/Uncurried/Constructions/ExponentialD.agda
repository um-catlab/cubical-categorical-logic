{-
  Displayed exponential
-}
{-# OPTIONS --lossy-unification #-}

-- This should probably be UniversalProperties.Exponential, not Constructions.Exponential
module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.More

import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Functorᴰ
open PshHom
open PshIso
open UniversalElementNotation
open UniversalElementᴰNotation
open isIsoOver

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ (P : LRPresheaf C ℓP) where
    isLRᴰ : (Pᴰ : Presheafᴰ (P .fst) Cᴰ ℓPᴰ) → Type _
    isLRᴰ Pᴰ = ∀ Γ (Γᴰ : Cᴰ.ob[ Γ ]) → UniversalElementᴰ Cᴰ ((C [-, Γ ]) ×Psh P .fst) ((Cᴰ [-][-, Γᴰ ]) ×ᴰPsh Pᴰ) (P .snd Γ)


module _ {C : Category ℓC ℓC'} (P : LRPresheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (ℓPᴰ : Level) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  LRᴰPresheafᴰ : Type _
  LRᴰPresheafᴰ = Σ (Presheafᴰ (P .fst) Cᴰ ℓPᴰ) (isLRᴰ P)

  module LRᴰPresheafᴰNotation (Pᴰ : LRᴰPresheafᴰ) where
    module P = PresheafNotation (P .fst)
    open PresheafᴰNotation Cᴰ (P .fst) (Pᴰ .fst) public

    private
      module ueᴰ {Γ}{Γᴰ} = UniversalElementᴰNotation Cᴰ _ _ (Pᴰ .snd Γ Γᴰ)

    open ueᴰ public

    _×ᴰPᴰ : ∀ {Γ} → Cᴰ.ob[ Γ ] → Cᴰ.ob[ P .snd Γ .vertex ]
    Γᴰ ×ᴰPᴰ = Pᴰ .snd _ Γᴰ .fst

    π₁ᴰ : ∀ {Γ}{Γᴰ} → Cᴰ [ P .snd Γ .element .fst ][ Γᴰ ×ᴰPᴰ , Γᴰ ]
    π₁ᴰ {Γ} {Γᴰ} = Pᴰ .snd Γ Γᴰ .snd .fst .fst

    π₂ᴰ : ∀ {Γ}{Γᴰ} → p[ P .snd Γ .element .snd ][ Γᴰ ×ᴰPᴰ ]
    π₂ᴰ {Γ} {Γᴰ} = Pᴰ .snd Γ Γᴰ .snd .fst .snd

    module _ {Γ A}{Γᴰ : Cᴰ.ob[ Γ ]}{Aᴰ : Cᴰ.ob[ A ]} where
      ×-cong-introᴰ : ∀ {f f' : C [ Γ , A ]}{p p' : P.p[ Γ ]}{fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]}{fᴰ' : Cᴰ [ f' ][ Γᴰ , Aᴰ ]}
        {pᴰ : p[ p ][ Γᴰ ]}
        {pᴰ' : p[ p' ][ Γᴰ ]}
        → fᴰ Cᴰ.∫≡ fᴰ'
        → pᴰ ∫≡ pᴰ'
        → ueᴰ.introᴰ (fᴰ , pᴰ) Cᴰ.∫≡ ueᴰ.introᴰ (fᴰ' , pᴰ')
      ×-cong-introᴰ fᴰ≡ pᴰ≡ = ueᴰ.cong-introᴰ (ΣPathPᴰ fᴰ≡ pᴰ≡)

      ×ηᴰ : ∀ {f,p : C [ Γ , P .snd A .vertex ]}
        {fᴰ,pᴰ : Cᴰ [ f,p ][ Γᴰ , Aᴰ ×ᴰPᴰ ]}
        → fᴰ,pᴰ Cᴰ.∫≡ ueᴰ.introᴰ (fᴰ,pᴰ Cᴰ.⋆ᴰ π₁ᴰ , fᴰ,pᴰ ⋆ᴰ π₂ᴰ)
      ×ηᴰ {f,p} {fᴰ,pᴰ} = ueᴰ.∫ηᴰ fᴰ,pᴰ ∙ ×-cong-introᴰ
        (sym (Cᴰ.reind-filler _ _))
        (⋆ᴰ-reind _ _ _)

      ×-introᴰ≡ : ∀ {f : C [ Γ , A ]}{p : P.p[ Γ ]}{f,p : C [ Γ , P .snd A .vertex ]}
        {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]}{pᴰ : p[ p ][ Γᴰ ]}
        {fᴰ,pᴰ : Cᴰ [ f,p ][ Γᴰ , Aᴰ ×ᴰPᴰ ]}
        → fᴰ Cᴰ.∫≡ (fᴰ,pᴰ Cᴰ.⋆ᴰ π₁ᴰ)
        → pᴰ ∫≡ (fᴰ,pᴰ ⋆ᴰ π₂ᴰ)
        → ueᴰ.introᴰ (fᴰ , pᴰ) Cᴰ.∫≡ fᴰ,pᴰ
      ×-introᴰ≡ fᴰ≡ pᴰ≡ = ×-cong-introᴰ fᴰ≡ pᴰ≡ ∙ sym ×ηᴰ

      module _ {f : C [ Γ , A ]} {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {p : P.p[ Γ ]} {pᴰ : p[ p ][ Γᴰ ]} where
        ×β₁ᴰ : (ueᴰ.introᴰ (fᴰ , pᴰ) Cᴰ.⋆ᴰ π₁ᴰ) Cᴰ.∫≡ fᴰ
        ×β₁ᴰ = Cᴰ.reind-filler _ _ ∙ PathPᴰΣ (ueᴰ.∫βᴰ (fᴰ , pᴰ)) .fst

        ×β₂ᴰ : (ueᴰ.introᴰ (fᴰ , pᴰ) ⋆ᴰ π₂ᴰ) ∫≡ pᴰ
        ×β₂ᴰ = sym (⋆ᴰ-reind _ _ _) ∙ PathPᴰΣ (ueᴰ.∫βᴰ (fᴰ , pᴰ)) .snd

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ {Q : Presheaf C ℓQ} (P : LRPresheaf C ℓP) (Pᴰ : LRᴰPresheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = LRᴰPresheafᴰNotation P Cᴰ _ Pᴰ
    -- TODO: uncurried functor comprehensionᴰ ?
    ×ᴰPᴰ-Fᴰ : Functorᴰ (LRPsh→Functor P) Cᴰ Cᴰ
    ×ᴰPᴰ-Fᴰ .F-obᴰ {Γ} Γᴰ = Γᴰ Pᴰ.×ᴰPᴰ
    ×ᴰPᴰ-Fᴰ .F-homᴰ {Δ} {Γ} {γ} {Δᴰ} {Γᴰ} γᴰ = Pᴰ.introᴰ ((Pᴰ.π₁ᴰ Cᴰ.⋆ᴰ γᴰ) , Pᴰ.π₂ᴰ)
    ×ᴰPᴰ-Fᴰ .F-idᴰ {x} {xᴰ} = Cᴰ.rectify $ Cᴰ.≡out $ Pᴰ.×-introᴰ≡
      (Cᴰ.⋆IdR _ ∙ sym (Cᴰ.⋆IdL _))
      (sym $ Pᴰ.formal-reind-filler _ _)
    ×ᴰPᴰ-Fᴰ .F-seqᴰ {x} {y} {z} {f} {g} {xᴰ} {yᴰ} {zᴰ} fᴰ gᴰ = Cᴰ.rectify $ Cᴰ.≡out $ Pᴰ.×-introᴰ≡
      (sym $ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ Pᴰ.×β₁ᴰ ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ Pᴰ.×β₁ᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _)
      (sym $ Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.×β₂ᴰ ⟩ ∙ Pᴰ.×β₂ᴰ)

    ×ᴰPᴰ : Functor (Cᴰ / (P ⇒PshSmall Q)) (Cᴰ / Q)
    ×ᴰPᴰ = _/Fᴰ_ {F = LRPsh→Functor P} ×ᴰPᴰ-Fᴰ idPshHom

    module _ (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
      Exponentialᴰ : Presheafᴰ (P ⇒PshSmall Q) Cᴰ ℓQᴰ
      Exponentialᴰ = reindPsh ×ᴰPᴰ Qᴰ
