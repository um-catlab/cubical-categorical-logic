{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.Exponential.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.IsoFib
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Profunctor

open Functor
open Functorᴰ
open PshHomᴰ

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

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ)
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    ∫⇒Large = (∫P Pᴰ) ⇒PshLarge (∫P Qᴰ)
    module ∫⇒Large = PresheafNotation ∫⇒Large

  -- could we use some kind of vertical variant of PshHomᴰProfᴰ
  _⇒PshLargeⱽ_ : Presheafᴰ P Cᴰ _
  _⇒PshLargeⱽ_ .F-obᴰ Γᴰ p =
    (PshHomᴰ (yoRec P p) ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ) Qᴰ)
    , isSetPshHomᴰ _ _ _
  -- βⱽ : PshHomⱽ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ) (reindYo p Qᴰ)
  ------------------------------------------------------------------
  -- ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo (f P.⋆ p) Pᴰ) (reindYo (f P.⋆ p) Qᴰ)
  _⇒PshLargeⱽ_ .F-homᴰ γᴰ p αᴰ =
    PshHomPathPshHomᴰ (sym $ yoRec≡ P P.⟨ sym $ C.⋆IdL _ ⟩⋆⟨⟩) $
      (yoRecᴰ _ γᴰ ×ⱽHom reind-introᴰ (PshHomPathPshHomᴰ (yoRec≡ P P.⟨ sym $ C.⋆IdL _ ⟩⋆⟨⟩) reind-π))
      ⋆PshHomᴰ αᴰ
  _⇒PshLargeⱽ_ .F-idᴰ = funExt (λ p → funExt (λ αⱽ →
    -- TODO: need to develop some better theory here...
    -- basically this is something like
    -- reind _ (yoRecᴰ id × reind _ reind-π) ⋆ᴰ αⱽ
    -- ≡[reind-filler] (yoRecᴰ id × reind-intro (reind _ reind-π)) ⋆ᴰ αⱽ
    -- ≡[] (id × id) ⋆ᴰ αⱽ
    -- ≡[] id ⋆ᴰ αⱽ
    -- ≡ αⱽ
    {!!}))
  _⇒PshLargeⱽ_ .F-seqᴰ = {!!}
  -- private
  --   ⇒PshLarge-test : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (α : ⟨ (P ⇒PshLarge Q) .F-ob Γ ⟩)
  --     → ⟨ _⇒PshLargeᴰ_ .F-obᴰ Γᴰ α ⟩ ≡ PshHomᴰ α ((Cᴰ [-][-, Γᴰ ]) ×ᴰPsh Pᴰ) Qᴰ
  --   ⇒PshLarge-test = λ Γᴰ α → refl

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
      module Pᴰ⇒LQᴰ = PresheafᴰNotation (Pᴰ ⇒PshLargeⱽ Qᴰ)

    open LocallyRepresentableⱽNotation Pᴰ _×ⱽ_*Pᴰ

    ⌈_⇒PshSmallⱽ_⌉ : ∀ {Γ} (p : P.p[ Γ ]) (Γᴰ : Cᴰ.ob[ Γ ]) → Type ℓQᴰ
    ⌈_⇒PshSmallⱽ_⌉ p Γᴰ = Qᴰ.p[ p ][ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]

    ⇒PshSmallⱽ-⋆ᴰ : ∀ {Δ Γ : C.ob} {Δᴰ : Cᴰ.ob[ Δ ]} {Γᴰ : Cᴰ.ob[ Γ ]}
      {γ  : C [ Δ , Γ ]} {p : P.p[ Γ ]}
      (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
      (qᴰ : ⌈_⇒PshSmallⱽ_⌉ p Γᴰ)
      → ⌈_⇒PshSmallⱽ_⌉ (γ P.⋆ p) Δᴰ
    ⇒PshSmallⱽ-⋆ᴰ γᴰ qᴰ = funcLR γᴰ Qᴰ.⋆ᴰ qᴰ

    ⌈⇒PshLargeⱽ≅⇒PshSmallⱽ⌉
      : {Γ : C.ob} (p : P.p[ Γ ]) (Γᴰ : Cᴰ.ob[ Γ ])
      → Iso (PshHomᴰ (yoRec P p) ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ) Qᴰ)
            Qᴰ.p[ p ][ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ ]
    ⌈⇒PshLargeⱽ≅⇒PshSmallⱽ⌉ = λ p Γᴰ →
      compIso
        (precomp⋆PshHomⱽᴰ-Iso (yoRecIsoⱽ (Γᴰ ×ⱽ p *Pᴰ)))
        (invIso $ yoRecᴰ-Iso Qᴰ) -- Yoneda

    private
      better-⌈⇒PshLargeⱽ≅⇒PshSmallⱽ⌉ : {Γ : C.ob} (p : P.p[ Γ ]) (Γᴰ : Cᴰ.ob[ Γ ])
        → (αᴰ : PshHomᴰ (yoRec P p) ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ) Qᴰ)
        → ⌈⇒PshLargeⱽ≅⇒PshSmallⱽ⌉ p Γᴰ .Iso.fun αᴰ
          -- ≡ Qᴰ.reind (P.⋆IdL p) (((yoRecIsoⱽ (Γᴰ ×ⱽ p *Pᴰ)) .fst ⋆PshHomⱽᴰ αᴰ) .N-obᴰ Cᴰ.idᴰ)
          ≡ (Qᴰ.reind (P.⋆IdL p) $ αᴰ .N-obᴰ (π₁LR Γᴰ p , π₂LR Γᴰ p))
      better-⌈⇒PshLargeⱽ≅⇒PshSmallⱽ⌉ p Γᴰ αᴰ = Qᴰ.rectify $ Qᴰ.≡out $
        Qᴰ.reind⟨ _ ⟩⟨ N-obᴰ⟨_⟩ αᴰ (×≡Snd-hSet C.isSetHom ((sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆IdL _)
          (change-base (P._⋆ p) P.isSetPsh refl
            (sym (Pᴰ.reind-filler _ _ ∙ Pᴰ.reind-filler _ _)
            ∙ Pᴰ.⋆IdL _))) ⟩

    opaque
      ⇒PshLargeⱽ'→⇒PshSmallⱽ-Nhomᴰ :
        {Δ Γ : C.ob} {Δᴰ : Cᴰ.ob[ Δ ]} {Γᴰ : Cᴰ.ob[ Γ ]}
        {γ : C [ Δ , Γ ]} {p : P.p[ Γ ]} (γᴰ : Cᴰ [ γ ][ Δᴰ , Γᴰ ])
        (αᴰ : PshHomᴰ (yoRec P p) ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ) Qᴰ)
        → ⌈⇒PshLargeⱽ≅⇒PshSmallⱽ⌉ _ _ .Iso.fun (γᴰ Pᴰ⇒LQᴰ.⋆ᴰ αᴰ)
          ≡ (funcLR γᴰ Qᴰ.⋆ᴰ ⌈⇒PshLargeⱽ≅⇒PshSmallⱽ⌉ _ _ .Iso.fun αᴰ)
      ⇒PshLargeⱽ'→⇒PshSmallⱽ-Nhomᴰ {Δ} {Γ} {Δᴰ} {Γᴰ} {γ} {p} γᴰ αᴰ =
        Qᴰ.rectify $ Qᴰ.≡out $
          sym (Qᴰ.reind-filler _ _ ∙ Qᴰ.reind-filler _ _)
          ∙ λ i → {!!}

    _⇒PshSmallⱽ'_ : Presheafᴰ P Cᴰ ℓQᴰ
    _⇒PshSmallⱽ'_ = pushⱽPshᴰ Cᴰ (Pᴰ ⇒PshLargeⱽ Qᴰ) ⌈_⇒PshSmallⱽ_⌉
      ⇒PshSmallⱽ-⋆ᴰ
      ⌈⇒PshLargeⱽ≅⇒PshSmallⱽ⌉
      ⇒PshLargeⱽ'→⇒PshSmallⱽ-Nhomᴰ

    -- Γᴰ ⊢ (Pᴰ ⇒ Qᴰ)(p) := Γᴰ , Pᴰ(p) ⊢ Qᴰ(p)
    _⇒PshSmallⱽ_ : Presheafᴰ P Cᴰ ℓQᴰ
    _⇒PshSmallⱽ_ .F-obᴰ {Γ} Γᴰ p = Qᴰ .F-obᴰ ⌈ Γᴰ ×ⱽ p *Pᴰ⌉ p
    _⇒PshSmallⱽ_ .F-homᴰ {Γ} {Δ} {γ} {Γᴰ} {Δᴰ} γᴰ p qᴰ = funcLR γᴰ Qᴰ.⋆ᴰ qᴰ
    _⇒PshSmallⱽ_ .F-idᴰ {Γ}{Γᴰ} = funExt λ p → funExt λ qᴰ →
      symP $ PresheafᴰNotation.toPathPPshᴰ Qᴰ ((cong ⌈ _ ×ⱽ_*Pᴰ⌉) (sym $ P.⋆IdL _)) $
        Qᴰ.⟨ sym $ introLR≡
          ((sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆IdR _)
          ∙ (sym $ PresheafᴰNotation.fromPathPPshᴰ (Cᴰ [-][-, _ ])
              (((cong ⌈ _ ×ⱽ_*Pᴰ⌉) (sym $ P.⋆IdL _)))
              (cong (π₁LR _) $ sym $ P.⋆IdL _)))
          (sym (PresheafᴰNotation.fromPathPPshᴰ Pᴰ (cong ⌈ _ ×ⱽ_*Pᴰ⌉ $ sym $ P.⋆IdL _)
            (cong (π₂LR _) (sym $ P.⋆IdL _)) ∙ Pᴰ.reind-filler _ _))
          ⟩⋆⟨⟩
    _⇒PshSmallⱽ_ .F-seqᴰ {Γ} {Δ} {Θ} {γ} {δ} {Γᴰ} {Δᴰ} {Θᴰ} γᴰ δᴰ = funExt λ p → funExt λ qᴰ →
      symP $ PresheafᴰNotation.toPathPPshᴰ Qᴰ (cong ⌈ _ ×ⱽ_*Pᴰ⌉ $ sym $ P.⋆Assoc _ _ _) $
        sym $
          Qᴰ.⟨
            introLR≡
              ((sym $ Cᴰ.reind-filler _ _)
              ∙ Cᴰ.⟨ sym $ PresheafᴰNotation.fromPathPPshᴰ (Cᴰ [-][-, _ ]) (cong ⌈ _ ×ⱽ_*Pᴰ⌉ $ sym $ P.⋆Assoc _ _ _)
                (cong (π₁LR Θᴰ) (sym $ P.⋆Assoc _ _ _))
                ⟩⋆⟨⟩
              ∙ (sym $
                Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ β₁LR _ _ ∙ sym (Cᴰ.reind-filler _ _) ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ β₁LR _ _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩ ∙ (sym $ Cᴰ.⋆Assoc _ _ _) ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _ ))
              ((sym $ Pᴰ.reind-filler _ _)
              ∙ (sym $ PresheafᴰNotation.fromPathPPshᴰ Pᴰ ((cong ⌈ _ ×ⱽ_*Pᴰ⌉ $ sym $ P.⋆Assoc _ _ _)) (cong (π₂LR _) (sym $ P.⋆Assoc _ _ _)))
              ∙ (sym $
                Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ β₂LR _ _ ∙ (sym $ Pᴰ.reind-filler _ _) ⟩ ∙ Pᴰ.⋆Assoc _ _ _ ∙ Pᴰ.⟨⟩⋆⟨ β₂LR _ _ ∙ (sym $ Pᴰ.reind-filler _ _) ⟩ ))
          ⟩⋆⟨⟩
          ∙ Qᴰ.⋆Assoc _ _ _
          ∙ Qᴰ.⋆Assoc _ _ _

    private
      testsmall : _⇒PshSmallⱽ_ ≡ _⇒PshSmallⱽ'_
      testsmall = Functorᴰ≡ (λ _ → funExt (λ _ → ΣPathP (refl , {!!}))) λ fᴰ → refl
