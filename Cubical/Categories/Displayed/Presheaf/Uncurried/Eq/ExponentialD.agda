{-
  Displayed exponential
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.ExponentialD where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.More


open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base

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
open isIsoOver

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ (P : LRPresheaf C ℓP) where
    isLRᴰ : (Pᴰ : Presheafᴰ (P .fst) Cᴰ ℓPᴰ) → Type _
    isLRᴰ Pᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ])
      → UEᴰ (PshAssocEq-fromPath _) (((Cᴰ [-][-, Γᴰ ]) ×ᴰPsh Pᴰ)) (P .snd Γ)

module _ {C : Category ℓC ℓC'} (P : LRPresheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (ℓPᴰ : Level) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  LRᴰPresheafᴰ : Type _
  LRᴰPresheafᴰ = Σ (Presheafᴰ (P .fst) Cᴰ ℓPᴰ) (isLRᴰ P)

  module LRᴰPresheafᴰNotation (Pᴰ : LRᴰPresheafᴰ) where
    module P = PresheafNotation (P .fst)
    open PresheafᴰNotation (Pᴰ .fst) public

    private
      module ueᴰ {Γ}{Γᴰ} = UEᴰ (Pᴰ .snd {Γ} Γᴰ)

    open ueᴰ public

    _×ᴰPᴰ : ∀ {Γ} → Cᴰ.ob[ Γ ] → Cᴰ.ob[ P .snd Γ .vertex ]
    Γᴰ ×ᴰPᴰ = vᴰ {Γᴰ = Γᴰ}

    π₁ᴰ : ∀ {Γ}{Γᴰ} → Cᴰ [ P .snd Γ .element .fst ][ Γᴰ ×ᴰPᴰ , Γᴰ ]
    π₁ᴰ {Γ} {Γᴰ} = eᴰ .fst

    π₂ᴰ : ∀ {Γ}{Γᴰ} → p[ P .snd Γ .element .snd ][ Γᴰ ×ᴰPᴰ ]
    π₂ᴰ {Γ} {Γᴰ} = eᴰ .snd

    module _ {Γ A}{Γᴰ : Cᴰ.ob[ Γ ]}{Aᴰ : Cᴰ.ob[ A ]} where
      ×-cong-introᴰ : ∀ {f f' : C [ Γ , A ]}{p p' : P.p[ Γ ]}{fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]}{fᴰ' : Cᴰ [ f' ][ Γᴰ , Aᴰ ]}
        {pᴰ : p[ p ][ Γᴰ ]}
        {pᴰ' : p[ p' ][ Γᴰ ]}
        → fᴰ Cᴰ.∫≡ fᴰ'
        → pᴰ ∫≡ pᴰ'
        → ueᴰ.introᴰ (fᴰ , pᴰ) Cᴰ.∫≡ ueᴰ.introᴰ (fᴰ' , pᴰ')
      ×-cong-introᴰ fᴰ≡ pᴰ≡ = ueᴰ.cong-introᴰ (ΣPathPᴰ fᴰ≡ pᴰ≡)

      ×-introᴰ≡ : ∀ {f : C [ Γ , A ]}{p : P.p[ Γ ]}{f,p : C [ Γ , P .snd A .vertex ]}
        {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]}{pᴰ : p[ p ][ Γᴰ ]}
        {fᴰ,pᴰ : Cᴰ [ f,p ][ Γᴰ , Aᴰ ×ᴰPᴰ ]}
        → fᴰ Cᴰ.∫≡ (fᴰ,pᴰ Cᴰ.⋆ᴰ π₁ᴰ)
        → pᴰ ∫≡ (fᴰ,pᴰ ⋆ᴰ π₂ᴰ)
        → ueᴰ.introᴰ (fᴰ , pᴰ) Cᴰ.∫≡ fᴰ,pᴰ
      ×-introᴰ≡ fᴰ≡ pᴰ≡ = ×-cong-introᴰ fᴰ≡ pᴰ≡ ∙ sym ∫ηᴰ

--     --   ×-extensionalityᴰ : ∀ {f,p f,p' : C [ Γ , P .snd A .vertex ]}
--     --     {fᴰ,pᴰ : Cᴰ [ f,p ][ Γᴰ , Aᴰ ×ᴰPᴰ ]}
--     --     {fᴰ,pᴰ' : Cᴰ [ f,p' ][ Γᴰ , Aᴰ ×ᴰPᴰ ]}
--     --     → (fᴰ,pᴰ Cᴰ.⋆ᴰ π₁ᴰ) Cᴰ.∫≡ (fᴰ,pᴰ' Cᴰ.⋆ᴰ π₁ᴰ)
--     --     → (fᴰ,pᴰ ⋆ᴰ π₂ᴰ) ∫≡ (fᴰ,pᴰ' ⋆ᴰ π₂ᴰ)
--     --     → fᴰ,pᴰ Cᴰ.∫≡ fᴰ,pᴰ'
--     --   ×-extensionalityᴰ 1≡ 2≡ = ×ηᴰ ∙ ×-introᴰ≡ 1≡ 2≡

      module _ {f : C [ Γ , A ]} {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {p : P.p[ Γ ]} {pᴰ : p[ p ][ Γᴰ ]} where
        -- fewer reinds!
        ×β₁ᴰ : (ueᴰ.introᴰ (fᴰ , pᴰ) Cᴰ.⋆ᴰ π₁ᴰ) Cᴰ.∫≡ fᴰ
        ×β₁ᴰ = PathPᴰΣ ueᴰ.∫βᴰ .fst

        ×β₂ᴰ : (ueᴰ.introᴰ (fᴰ , pᴰ) ⋆ᴰ π₂ᴰ) ∫≡ pᴰ
        ×β₂ᴰ = PathPᴰΣ ueᴰ.∫βᴰ .snd

    -- TODO: uncurried functor comprehensionᴰ ?
    ×ᴰPᴰ-Fᴰ : Functorᴰ (LRPsh→Functor P) Cᴰ Cᴰ
    ×ᴰPᴰ-Fᴰ .F-obᴰ {Γ} Γᴰ = Γᴰ ×ᴰPᴰ
    ×ᴰPᴰ-Fᴰ .F-homᴰ {Δ} {Γ} {γ} {Δᴰ} {Γᴰ} γᴰ = ueᴰ.introᴰ ((π₁ᴰ Cᴰ.⋆ᴰ γᴰ) , π₂ᴰ)
    ×ᴰPᴰ-Fᴰ .F-idᴰ {x} {xᴰ} = Cᴰ.rectifyOut $ ×-introᴰ≡
      (Cᴰ.⋆IdR _ ∙ sym (Cᴰ.⋆IdL _))
      (sym $ ⋆IdL _)
    ×ᴰPᴰ-Fᴰ .F-seqᴰ {x} {y} {z} {f} {g} {xᴰ} {yᴰ} {zᴰ} fᴰ gᴰ = Cᴰ.rectifyOut $ ×-introᴰ≡
      (sym (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ ×β₁ᴰ ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ ×β₁ᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _))
      (sym (⋆Assoc _ _ _ ∙ ⟨⟩⋆⟨ ×β₂ᴰ ⟩ ∙ ×β₂ᴰ))

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ {Q : Presheaf C ℓQ} (P : LRPresheaf C ℓP) (Pᴰ : LRᴰPresheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = LRᴰPresheafᴰNotation P Cᴰ _ Pᴰ
    ×ᴰPᴰ : Functor (Cᴰ / (P ⇒PshSmall Q)) (Cᴰ / Q)
    ×ᴰPᴰ = _/Fᴰ_ {F = LRPsh→Functor P} Pᴰ.×ᴰPᴰ-Fᴰ idPshHomEq

    module _ (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
      ⇒ᴰPshSmall : Presheafᴰ (P ⇒PshSmall Q) Cᴰ ℓQᴰ
      ⇒ᴰPshSmall = reindPsh ×ᴰPᴰ Qᴰ

LROb : Category ℓC ℓC' → Type _
LROb C = Σ C.ob (BinProductsWith C)
  where module C = Category C

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ ((A , _×A) : LROb C) where
    isLRᴰObᴰ : Cᴰ.ob[ A ] → Type _
    isLRᴰObᴰ Aᴰ = isLRᴰ ((C [-, A ]) , _×A) (Cᴰ [-][-, Aᴰ ])

    LRᴰObᴰ = Σ Cᴰ.ob[ A ] isLRᴰObᴰ
    module _ ((Aᴰ , _×ᴰAᴰ): LRᴰObᴰ) where
      ExponentialᴰSpec : ∀ {B} (Bᴰ : Cᴰ.ob[ B ]) → Exponential C A B _×A
        → Presheafᴰ (((C [-, A ]) , _×A) ⇒PshSmall (C [-, B ])) Cᴰ ℓCᴰ'
      ExponentialᴰSpec {B} Bᴰ A⇒B = ⇒ᴰPshSmall _ ((Cᴰ [-][-, Aᴰ ]) , _×ᴰAᴰ) (Cᴰ [-][-, Bᴰ ])

      Exponentialᴰ : ∀ {B} (Bᴰ : Cᴰ.ob[ B ]) → Exponential C A B _×A → Type _
      Exponentialᴰ {B} Bᴰ A⇒B = UEᴰ (PshAssocEq-fromPath _) (ExponentialᴰSpec Bᴰ A⇒B) A⇒B

      Exponentiableᴰ : Exponentiable C A _×A → Type _
      Exponentiableᴰ A⇒_ = ∀ {B} Bᴰ → Exponentialᴰ {B = B} Bᴰ (A⇒ B)

  module _ (bp : BinProducts C) (bpᴰ : BinProductsᴰ Cᴰ bp) where
    AllExponentiableᴰ : AllExponentiable C bp → Type _
    AllExponentiableᴰ _⇒_ = ∀ {A} (Aᴰ : Cᴰ.ob[ A ])
      → Exponentiableᴰ (A , (λ c → bp (c , A))) (Aᴰ , (λ Γᴰ → bpᴰ Γᴰ Aᴰ)) (A ⇒_)
