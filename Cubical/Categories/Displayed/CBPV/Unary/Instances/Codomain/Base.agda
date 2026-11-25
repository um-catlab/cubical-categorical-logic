{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ {x y} {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
    (π : Cᴰ [ f ][ xᴰ , yᴰ ])
    (intro : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g : C [ Γ , x ]}
      → Cᴰ [ g C.⋆ f ][ Γᴰ , yᴰ ] → Cᴰ [ g ][ Γᴰ , xᴰ ])
    (β : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g : C [ Γ , x ]}
      (φ : Cᴰ [ g C.⋆ f ][ Γᴰ , yᴰ ]) → intro φ Cᴰ.⋆ᴰ π ≡ φ)
    (η : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g : C [ Γ , x ]}
      (ψ : Cᴰ [ g ][ Γᴰ , xᴰ ]) → intro (ψ Cᴰ.⋆ᴰ π) ≡ ψ)
    where
    mkCartesianLift : CartesianLift Cᴰ f yᴰ
    mkCartesianLift .fst = xᴰ
    mkCartesianLift .snd = Isos→PshIso
      (λ _ → iso (λ ψ → ψ Cᴰ.⋆ᴰ π) intro β η)
      λ _ _ _ _ → Cᴰ.rectifyOut
        (Cᴰ.⟨ Cᴰ.reind-filler⁻ _ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.reind-filler _)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ {x} (v : Cᴰ.ob[ x ])
    (! : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g : C [ Γ , x ]} → Cᴰ [ g ][ Γᴰ , v ])
    (!-η : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g : C [ Γ , x ]} (ψ : Cᴰ [ g ][ Γᴰ , v ])
      → ! ≡ ψ)
    where
    mkTerminalⱽ : Terminalⱽ Cᴰ x
    mkTerminalⱽ .fst = v
    mkTerminalⱽ .snd = Isos→PshIso
      (λ _ → iso (λ _ → tt) (λ _ → !) (λ _ → refl) !-η)
      λ _ _ _ _ → refl

  module _ ⦃ cr : ChosenReind Cᴰ ⦄ {x} {A B : Cᴰ.ob[ x ]} (v : Cᴰ.ob[ x ])
    (π₁ : Cᴰ [ C.id ][ v , A ]) (π₂ : Cᴰ [ C.id ][ v , B ])
    (pair : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g : C [ Γ , x ]}
      → Cᴰ [ g ][ Γᴰ , A ] → Cᴰ [ g ][ Γᴰ , B ] → Cᴰ [ g ][ Γᴰ , v ])
    where
    private
      module CR = ChosenReindNotation Cᴰ

      unpair : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g : C [ Γ , x ]}
        → Cᴰ [ g ][ Γᴰ , v ] → Cᴰ [ g ][ Γᴰ , A ] × Cᴰ [ g ][ Γᴰ , B ]
      unpair {g = g} ψ =
        CR.reind⟨ C.⋆IdR g ⟩ (ψ Cᴰ.⋆ᴰ π₁) , CR.reind⟨ C.⋆IdR g ⟩ (ψ Cᴰ.⋆ᴰ π₂)

    module _
      (pair-β : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g : C [ Γ , x ]}
        (φ : Cᴰ [ g ][ Γᴰ , A ] × Cᴰ [ g ][ Γᴰ , B ])
        → unpair (pair (φ .fst) (φ .snd)) ≡ φ)
      (pair-η : ∀ {Γ} {Γᴰ : Cᴰ.ob[ Γ ]} {g : C [ Γ , x ]}
        (ψ : Cᴰ [ g ][ Γᴰ , v ])
        → pair (unpair ψ .fst) (unpair ψ .snd) ≡ ψ)
      where
      mkBinProductⱽ : BinProductⱽ Cᴰ A B
      mkBinProductⱽ .fst = v
      mkBinProductⱽ .snd = Isos→PshIso
        (λ _ → iso unpair (λ φ → pair (φ .fst) (φ .snd)) pair-β pair-η)
        λ _ _ _ _ → ΣPathP
          ( Cᴰ.rectifyOut (CR.reind-∫≡ _ _ ∙ Cᴰ.⟨ Cᴰ.reind-filler⁻ _ ⟩⋆⟨⟩
              ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ sym (CR.reind-∫≡ _ _) ⟩
              ∙ Cᴰ.reind-filler _)
          , Cᴰ.rectifyOut (CR.reind-∫≡ _ _ ∙ Cᴰ.⟨ Cᴰ.reind-filler⁻ _ ⟩⋆⟨⟩
              ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ sym (CR.reind-∫≡ _ _) ⟩
              ∙ Cᴰ.reind-filler _))
