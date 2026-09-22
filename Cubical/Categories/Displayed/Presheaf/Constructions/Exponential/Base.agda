{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Exponential.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure


open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
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

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    ∫⇒Large = (∫P Pᴰ) ⇒PshLarge (∫P Qᴰ)
    module ∫⇒Large = PresheafNotation ∫⇒Large
  _⇒PshLargeᴰ_ : Presheafᴰ (P ⇒PshLarge Q) Cᴰ _
  _⇒PshLargeᴰ_ = PshHomᴰProfᴰ C Cᴰ .F-obᴰ Qᴰ ∘Fᴰ ((appRᴰ PshProdᴰ Pᴰ ∘Fᴰ YOᴰ) ^opFᴰ)
  private
    ⇒PshLarge-test : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (α : ⟨ (P ⇒PshLarge Q) .F-ob Γ ⟩)
      → ⟨ _⇒PshLargeᴰ_ .F-obᴰ Γᴰ α ⟩ ≡ PshHomᴰ α ((Cᴰ [-][-, Γᴰ ]) ×ᴰPsh Pᴰ) Qᴰ
    ⇒PshLarge-test = λ Γᴰ α → refl

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  where
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
    _⇒PshSmallᴰ_ .F-idᴰ {Γ} {Γᴰ} = funExt λ q → funExt λ qᴰ → Qᴰ.rectifyOut $
      funExt⁻ (∫⇒Small .F-id) (q , qᴰ)
    _⇒PshSmallᴰ_ .F-seqᴰ γᴰ δᴰ = funExt λ q → funExt λ qᴰ → Qᴰ.rectifyOut $
      funExt⁻ (∫⇒Small .F-seq (_ , γᴰ) (_ , δᴰ)) (q , qᴰ)

  -- TODO: ⇒PshLargeⱽ
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

    -- this breaks if we make presheafnotation opaque...

    -- Γᴰ ⊢ (Pᴰ ⇒ Qᴰ)(p) := Γᴰ , Pᴰ(p) ⊢ Qᴰ(p)
    _⇒PshSmallⱽ_ : Presheafᴰ P Cᴰ ℓQᴰ
    _⇒PshSmallⱽ_ .F-obᴰ {Γ} Γᴰ p = Qᴰ .F-obᴰ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ p
    _⇒PshSmallⱽ_ .F-homᴰ {Γ} {Δ} {γ} {Γᴰ} {Δᴰ} γᴰ p qᴰ = funcLR γᴰ Qᴰ.⋆ᴰ qᴰ
    _⇒PshSmallⱽ_ .F-idᴰ {Γ}{Γᴰ} =
      funExt λ p → funExt λ qᴰ →
      let e = sym $ P.⋆IdL p
          ⌈e⌉ = cong ⌈ Γᴰ ×ⱽ_*Pᴰ⌉ e in
      symP $ PresheafᴰNotation.toPathPPshᴰ Qᴰ ⌈e⌉ $
        Qᴰ.⟨ sym $ introLR≡
          ((sym (Cᴰ.reind-filler _) ∙ Cᴰ.⋆IdR _)
          ∙ (sym $ PresheafᴰNotation.fromPathPPshᴰ (Cᴰ [-][-, Γᴰ ]) ⌈e⌉
              (cong (π₁LR Γᴰ) e)))
          (sym (PresheafᴰNotation.fromPathPPshᴰ Pᴰ ⌈e⌉
            (cong (π₂LR Γᴰ) e) ∙ Pᴰ.reind-filler _))
          ⟩⋆⟨⟩
    _⇒PshSmallⱽ_ .F-seqᴰ {Γ} {Δ} {Θ} {γ} {δ} {Γᴰ} {Δᴰ} {Θᴰ} γᴰ δᴰ = funExt λ p → funExt λ qᴰ →
      let e = sym $ P.⋆Assoc δ γ p
          ⌈e⌉ = cong ⌈ Θᴰ ×ⱽ_*Pᴰ⌉ e in
      symP $ PresheafᴰNotation.toPathPPshᴰ Qᴰ ⌈e⌉ $ sym $
        Qᴰ.⟨ introLR≡ (((sym $ Cᴰ.reind-filler _)
              ∙ Cᴰ.⟨ sym $ PresheafᴰNotation.fromPathPPshᴰ (Cᴰ [-][-, Θᴰ ]) ⌈e⌉
                (cong (π₁LR Θᴰ) e)
                ⟩⋆⟨⟩
              ∙ (sym $
                Cᴰ.⋆Assoc _ _ _
                ∙ Cᴰ.⟨⟩⋆⟨ β₁LR {Γᴰ = Γᴰ}{p = p} _ _
                          ∙ sym (Cᴰ.reind-filler _) ⟩
                ∙ sym (Cᴰ.⋆Assoc _ _ _)
                ∙ Cᴰ.⟨ Cᴰ.⋆Assoc _ _ _
                     ∙ Cᴰ.⟨⟩⋆⟨ β₁LR {Γᴰ = Δᴰ}{p = γ P.⋆ p} _ _
                               ∙ (sym $ Cᴰ.reind-filler _) ⟩
                     ∙ (sym $ Cᴰ.⋆Assoc _ _ _) ⟩⋆⟨⟩
                ∙ Cᴰ.⋆Assoc _ _ _ )))
                ((sym $ Pᴰ.reind-filler _) ∙ (sym $ PresheafᴰNotation.fromPathPPshᴰ Pᴰ ⌈e⌉ (cong (π₂LR Θᴰ) e))
                ∙ (sym $
                Pᴰ.⋆Assoc _ _ _
                ∙ Pᴰ.⟨⟩⋆⟨ β₂LR {Γᴰ = Γᴰ}{p = p} _ _
                          ∙ (sym $ Pᴰ.reind-filler _) ⟩
                ∙ Pᴰ.⋆Assoc _ _ _
                ∙ Pᴰ.⟨⟩⋆⟨ β₂LR {Γᴰ = Δᴰ}{p = γ P.⋆ p} _ _
                          ∙ (sym $ Pᴰ.reind-filler _) ⟩ ))
        ⟩⋆⟨⟩
        ∙ Qᴰ.⋆Assoc _ _ _ ∙ Qᴰ.⋆Assoc _ _ _
