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
open import Cubical.Categories.Exponentials.Small
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
    isLRᴰ Pᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ])
      → UniversalElementᴰ Cᴰ ((C [-, Γ ]) ×Psh P .fst) ((Cᴰ [-][-, Γᴰ ]) ×ᴰPsh Pᴰ) (P .snd Γ)

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
      module ueᴰ {Γ}{Γᴰ} = UniversalElementᴰNotation Cᴰ _ _ (Pᴰ .snd {Γ} Γᴰ)

    open ueᴰ public

    _×ᴰPᴰ : ∀ {Γ} → Cᴰ.ob[ Γ ] → Cᴰ.ob[ P .snd Γ .vertex ]
    Γᴰ ×ᴰPᴰ = Pᴰ .snd  Γᴰ .fst

    π₁ᴰ : ∀ {Γ}{Γᴰ} → Cᴰ [ P .snd Γ .element .fst ][ Γᴰ ×ᴰPᴰ , Γᴰ ]
    π₁ᴰ {Γ} {Γᴰ} = Pᴰ .snd {Γ} Γᴰ .snd .fst .fst

    π₂ᴰ : ∀ {Γ}{Γᴰ} → p[ P .snd Γ .element .snd ][ Γᴰ ×ᴰPᴰ ]
    π₂ᴰ {Γ} {Γᴰ} = Pᴰ .snd {Γ} Γᴰ .snd .fst .snd

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

      ×-extensionalityᴰ : ∀ {f,p f,p' : C [ Γ , P .snd A .vertex ]}
        {fᴰ,pᴰ : Cᴰ [ f,p ][ Γᴰ , Aᴰ ×ᴰPᴰ ]}
        {fᴰ,pᴰ' : Cᴰ [ f,p' ][ Γᴰ , Aᴰ ×ᴰPᴰ ]}
        → (fᴰ,pᴰ Cᴰ.⋆ᴰ π₁ᴰ) Cᴰ.∫≡ (fᴰ,pᴰ' Cᴰ.⋆ᴰ π₁ᴰ)
        → (fᴰ,pᴰ ⋆ᴰ π₂ᴰ) ∫≡ (fᴰ,pᴰ' ⋆ᴰ π₂ᴰ)
        → fᴰ,pᴰ Cᴰ.∫≡ fᴰ,pᴰ'
      ×-extensionalityᴰ 1≡ 2≡ = ×ηᴰ ∙ ×-introᴰ≡ 1≡ 2≡

      module _ {f : C [ Γ , A ]} {fᴰ : Cᴰ [ f ][ Γᴰ , Aᴰ ]} {p : P.p[ Γ ]} {pᴰ : p[ p ][ Γᴰ ]} where
        ×β₁ᴰ : (ueᴰ.introᴰ (fᴰ , pᴰ) Cᴰ.⋆ᴰ π₁ᴰ) Cᴰ.∫≡ fᴰ
        ×β₁ᴰ = Cᴰ.reind-filler _ _ ∙ PathPᴰΣ (ueᴰ.∫βᴰ (fᴰ , pᴰ)) .fst

        ×β₂ᴰ : (ueᴰ.introᴰ (fᴰ , pᴰ) ⋆ᴰ π₂ᴰ) ∫≡ pᴰ
        ×β₂ᴰ = sym (⋆ᴰ-reind _ _ _) ∙ PathPᴰΣ (ueᴰ.∫βᴰ (fᴰ , pᴰ)) .snd

    -- TODO: uncurried functor comprehensionᴰ ?
    ×ᴰPᴰ-Fᴰ : Functorᴰ (LRPsh→Functor P) Cᴰ Cᴰ
    ×ᴰPᴰ-Fᴰ .F-obᴰ {Γ} Γᴰ = Γᴰ ×ᴰPᴰ
    ×ᴰPᴰ-Fᴰ .F-homᴰ {Δ} {Γ} {γ} {Δᴰ} {Γᴰ} γᴰ = ueᴰ.introᴰ ((π₁ᴰ Cᴰ.⋆ᴰ γᴰ) , π₂ᴰ)
    ×ᴰPᴰ-Fᴰ .F-idᴰ {x} {xᴰ} = Cᴰ.rectify $ Cᴰ.≡out $ ×-introᴰ≡
      (Cᴰ.⋆IdR _ ∙ sym (Cᴰ.⋆IdL _))
      (sym $ formal-reind-filler _ _)
    ×ᴰPᴰ-Fᴰ .F-seqᴰ {x} {y} {z} {f} {g} {xᴰ} {yᴰ} {zᴰ} fᴰ gᴰ = Cᴰ.rectify $ Cᴰ.≡out $ ×-introᴰ≡
      (sym $ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ ×β₁ᴰ ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ ×β₁ᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _)
      (sym $ ⋆Assoc _ _ _ ∙ ⟨⟩⋆⟨ ×β₂ᴰ ⟩ ∙ ×β₂ᴰ)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ {Q : Presheaf C ℓQ} (P : LRPresheaf C ℓP) (Pᴰ : LRᴰPresheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = LRᴰPresheafᴰNotation P Cᴰ _ Pᴰ
    ×ᴰPᴰ : Functor (Cᴰ / (P ⇒PshSmall Q)) (Cᴰ / Q)
    ×ᴰPᴰ = _/Fᴰ_ {F = LRPsh→Functor P} Pᴰ.×ᴰPᴰ-Fᴰ idPshHom

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
      Exponentialᴰ {B} Bᴰ A⇒B =
        UniversalElementᴰ Cᴰ
          (((C [-, A ]) , _×A) ⇒PshSmall (C [-, B ]))
          (ExponentialᴰSpec Bᴰ A⇒B)
          A⇒B

      Exponentiableᴰ : Exponentiable C A _×A → Type _
      Exponentiableᴰ A⇒_ = ∀ {B} Bᴰ → Exponentialᴰ {B = B} Bᴰ (A⇒ B)

  module _ (bp : BinProducts C) (bpᴰ : BinProductsᴰ Cᴰ bp) where
    AllExponentiableᴰ : AllExponentiable C bp → Type _
    AllExponentiableᴰ _⇒_ = ∀ {A} (Aᴰ : Cᴰ.ob[ A ])
      → Exponentiableᴰ (A , (λ c → bp (c , A))) (Aᴰ , (λ Γᴰ → bpᴰ Γᴰ Aᴰ)) (A ⇒_)

-- Notations
module ExponentialᴰNotation {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {(A , _×A) : LROb C}
  {(Aᴰ , _×ᴰAᴰ) : LRᴰObᴰ Cᴰ (A , _×A)}
  {B}{Bᴰ}
  (A⇒B : Exponential C A B _×A)
  (Aᴰ⇒ᴰBᴰ : Exponentialᴰ Cᴰ (A , _×A) (Aᴰ , _×ᴰAᴰ) Bᴰ A⇒B)
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module -×A = BinProductsWithNotation _×A
    module -×ᴰAᴰ = LRᴰPresheafᴰNotation (_ , _×A) Cᴰ _ (_ , _×ᴰAᴰ)
    module A⇒B = ExponentialNotation {C = C} _×A A⇒B
    module Aᴰ⇒BᴰPshᴰ = PresheafᴰNotation Cᴰ (((C [-, A ]) , _×A) ⇒PshSmall (C [-, B ]))
      (⇒ᴰPshSmall _ ((Cᴰ [-][-, Aᴰ ]) , _×ᴰAᴰ) (Cᴰ [-][-, Bᴰ ]))
    module ueᴰ = UniversalElementᴰNotation Cᴰ (((C [-, A ]) , _×A) ⇒PshSmall (C [-, B ])) (⇒ᴰPshSmall ((C [-, A ]) , _×A) ((Cᴰ [-][-, Aᴰ ]) , _×ᴰAᴰ) (Cᴰ [-][-, Bᴰ ])) Aᴰ⇒ᴰBᴰ

    _impr⋆ᴰ_ : ∀ {Δ Γ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γᴰ : Cᴰ.ob[ Γ ]}
      {γ : C [ Δ , Γ ]}
      {f : C [ (Γ ×A) .vertex , B ]}
      (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
      (fᴰ : Cᴰ [ f ][ Γᴰ -×ᴰAᴰ.×ᴰPᴰ , Bᴰ ])
      → Cᴰ [ LRPsh→Functor (_ , _×A) ⟪ γ ⟫ C.⋆ f ][ Δᴰ -×ᴰAᴰ.×ᴰPᴰ , Bᴰ ]
    γᴰ impr⋆ᴰ fᴰ = -×ᴰAᴰ.×ᴰPᴰ-Fᴰ .F-homᴰ γᴰ Cᴰ.⋆ᴰ fᴰ

  opaque
    impr≡compositional⋆ᴰ : ∀ {Δ Γ}{Δᴰ : Cᴰ.ob[ Δ ]}{Γᴰ : Cᴰ.ob[ Γ ]}
      {γ : C [ Δ , Γ ]}
      {f : C [ (Γ ×A) .vertex , B ]}
      (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
      (fᴰ : Cᴰ [ f ][ Γᴰ -×ᴰAᴰ.×ᴰPᴰ , Bᴰ ])
      → (γᴰ impr⋆ᴰ fᴰ) Cᴰ.∫≡ (γᴰ Aᴰ⇒BᴰPshᴰ.⋆ᴰ fᴰ)
    impr≡compositional⋆ᴰ {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {f} γᴰ fᴰ = Cᴰ.reind-filler _ _

    λᴰ : ∀ {Γ}{Γᴰ}{f : C [ (Γ ×A) .vertex , B ]}
      → Cᴰ [ f ][  Γᴰ -×ᴰAᴰ.×ᴰPᴰ , Bᴰ ]
      → Cᴰ [ A⇒B.lda f ][ Γᴰ , Aᴰ⇒ᴰBᴰ .fst ]
    λᴰ = ueᴰ.introᴰ

    cong-λᴰ : ∀ {Γ}{Γᴰ}{f g : C [ (Γ ×A) .vertex , B ]}
      → {fᴰ : Cᴰ [ f ][  Γᴰ -×ᴰAᴰ.×ᴰPᴰ , Bᴰ ]}
      → {gᴰ : Cᴰ [ g ][  Γᴰ -×ᴰAᴰ.×ᴰPᴰ , Bᴰ ]}
      → fᴰ Cᴰ.∫≡ gᴰ
      → λᴰ fᴰ Cᴰ.∫≡ λᴰ gᴰ
    cong-λᴰ fᴰ≡gᴰ = ueᴰ.cong-introᴰ fᴰ≡gᴰ

    appᴰ : Cᴰ [ A⇒B.app ][ Aᴰ⇒ᴰBᴰ .fst -×ᴰAᴰ.×ᴰPᴰ , Bᴰ ]
    appᴰ = ueᴰ.elementᴰ

    ⇒βᴰ : ∀ {Γ}{Γᴰ}{f : C [ (Γ ×A) .vertex , B ]}
      → (fᴰ : Cᴰ [ f ][  Γᴰ -×ᴰAᴰ.×ᴰPᴰ , Bᴰ ])
      → (-×ᴰAᴰ.introᴰ ((-×ᴰAᴰ.π₁ᴰ Cᴰ.⋆ᴰ λᴰ fᴰ) , -×ᴰAᴰ.π₂ᴰ) Cᴰ.⋆ᴰ appᴰ) Cᴰ.∫≡ fᴰ
    ⇒βᴰ fᴰ = impr≡compositional⋆ᴰ _ _ ∙ (Cᴰ.≡in $ ueᴰ.βᴰ fᴰ)

    ⇒ηᴰ : ∀ {Γ}{Γᴰ}{f : C [ Γ , A⇒B.⇒ue.vertex ]}
      → (fᴰ : Cᴰ [ f ][  Γᴰ , Aᴰ⇒ᴰBᴰ .fst ])
      → fᴰ Cᴰ.∫≡ λᴰ (-×ᴰAᴰ.×ᴰPᴰ-Fᴰ .F-homᴰ fᴰ Cᴰ.⋆ᴰ appᴰ)
    ⇒ηᴰ fᴰ = (Cᴰ.≡in $ ueᴰ.ηᴰ fᴰ) ∙ ueᴰ.cong-introᴰ (sym $ impr≡compositional⋆ᴰ _ _)

module ExponentialsᴰNotation {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (bp : BinProducts C) (bpᴰ : BinProductsᴰ Cᴰ bp)
  (_⇒_ : AllExponentiable C bp) (_⇒ᴰ_ : AllExponentiableᴰ Cᴰ bp bpᴰ _⇒_) where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module ueᴰ {A}{B}{Aᴰ : Cᴰ.ob[ A ]}{Bᴰ : Cᴰ.ob[ B ]} = ExponentialᴰNotation (A ⇒ B) (Aᴰ ⇒ᴰ Bᴰ)

  open ueᴰ public
