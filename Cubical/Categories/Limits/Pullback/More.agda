{-

  Definition

       D
       |
       \/
  C -> E

-}

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Limits.Pullback.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓR ℓS : Level

open Category
open Functor
open Iso
open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where

  mapCospan : Functor C D → Cospan C → Cospan D
  mapCospan F s = cospan
    (F ⟅ s .Cospan.l ⟆)
    (F ⟅ s .Cospan.m ⟆)
    (F ⟅ s .Cospan.r ⟆)
    (F ⟪ s .Cospan.s₁ ⟫)
    (F ⟪ s .Cospan.s₂ ⟫)

  PreservesPullbacks : Functor C D → Type _
  PreservesPullbacks F =
    ∀ {s : Cospan C} {c : C .ob}
      {p₁ : C [ c , s .Cospan.l ]} {p₂ : C [ c , s .Cospan.r ]}
      {commutes : p₁ ⋆⟨ C ⟩ s .Cospan.s₁ ≡ p₂ ⋆⟨ C ⟩ s .Cospan.s₂}
    → isPullback C s p₁ p₂ commutes
    → isPullback D (mapCospan F s)
        (F ⟪ p₁ ⟫) (F ⟪ p₂ ⟫) (F-square F commutes)

module _ {C : Category ℓC ℓC'} where

  PointwiseContr→PreservesPullbacks :
    (F : Functor C (SET ℓS)) →
    ((c : C .ob) → isContr ⟨ F ⟅ c ⟆ ⟩) →
    PreservesPullbacks F
  PointwiseContr→PreservesPullbacks F contr pb {d} h k H =
    uniqueExists
      (λ _ → contr _ .fst)
      ( funExt (λ _ → isContr→isProp (contr _) _ _)
      , funExt (λ _ → isContr→isProp (contr _) _ _))
      (λ _ → isProp×
        ((isSet→ (isProp→isSet (isContr→isProp (contr _)))) _ _)
      ((isSet→ (isProp→isSet (isContr→isProp (contr _)))) _ _))
      (λ q _ → funExt λ x → isContr→isProp (contr _) _ (q x))

  PointwiseProductPreservesPullbacks :
    (F G : Functor C (SET ℓS)) →
    PreservesPullbacks F →
    PreservesPullbacks G →
    PreservesPullbacks (×Sets ∘F (F ,F G))
  PointwiseProductPreservesPullbacks F G F-pb G-pb
    {s} {c} {p₁} {p₂} {commutes} pb {d} h k H =
    uniqueExists mediator
      ( (funExt λ x → ΣPathP
          ( funExt⁻ (F-cone .fst .snd .fst) x
          , funExt⁻ (G-cone .fst .snd .fst) x))
      , (funExt λ x → ΣPathP
          ( funExt⁻ (F-cone .fst .snd .snd) x
          , funExt⁻ (G-cone .fst .snd .snd) x)))
      (λ _ → isProp×
        ((isSet→ (isSet× ((F ⟅ _ ⟆) .snd) ((G ⟅ _ ⟆) .snd))) _ _)
        ((isSet→ (isSet× ((F ⟅ _ ⟆) .snd) ((G ⟅ _ ⟆) .snd))) _ _))
      (λ q equations → funExt λ x → ΣPathP
        ( funExt⁻ (cong fst (F-cone .snd
            ( (λ y → q y .fst)
            , funExt (λ y → cong fst (funExt⁻ (equations .fst) y))
            , funExt (λ y → cong fst (funExt⁻ (equations .snd) y))))) x
        , funExt⁻ (cong fst (G-cone .snd
            ( (λ y → q y .snd)
            , funExt (λ y → cong snd (funExt⁻ (equations .fst) y))
            , funExt (λ y → cong snd (funExt⁻ (equations .snd) y))))) x))
    where
    F-cone :
      ∃![ q ∈ (⟨ d ⟩ → ⟨ F ⟅ c ⟆ ⟩) ]
        ((λ x → h x .fst) ≡ (λ x → (F ⟪ p₁ ⟫) (q x))) ×
        ((λ x → k x .fst) ≡ (λ x → (F ⟪ p₂ ⟫) (q x)))
    F-cone = F-pb
      {s = s} {c = c} {p₁ = p₁} {p₂ = p₂} {commutes = commutes} pb
      {d = d}
      (λ x → h x .fst) (λ x → k x .fst)
      (funExt λ x → cong fst (funExt⁻ H x))

    G-cone :
      ∃![ q ∈ (⟨ d ⟩ → ⟨ G ⟅ c ⟆ ⟩) ]
        ((λ x → h x .snd) ≡ (λ x → (G ⟪ p₁ ⟫) (q x))) ×
        ((λ x → k x .snd) ≡ (λ x → (G ⟪ p₂ ⟫) (q x)))
    G-cone = G-pb
      {s = s} {c = c} {p₁ = p₁} {p₂ = p₂} {commutes = commutes} pb
      {d = d}
      (λ x → h x .snd) (λ x → k x .snd)
      (funExt λ x → cong snd (funExt⁻ H x))

    mediator : ⟨ d ⟩ → ⟨ F ⟅ c ⟆ ⟩ × ⟨ G ⟅ c ⟆ ⟩
    mediator = λ x → F-cone .fst .fst x , G-cone .fst .fst x

module _ (C : Category ℓ ℓ') where
  private
    module C = Category C
  module _ {cospan : Cospan C} (pb : Pullback C cospan) where
    open Cospan cospan
    open Pullback pb

    pullbackExtensionality : ∀ {Γ}{f g : C [ Γ , pbOb ]}
      → (f C.⋆ pbPr₁) ≡ (g C.⋆ pbPr₁)
      → (f C.⋆ pbPr₂) ≡ (g C.⋆ pbPr₂)
      → f ≡ g
    pullbackExtensionality f1≡g1 f2≡g2 = (sym $ pullbackArrowUnique {H = C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pbCommutes ⟩ ∙ sym (C.⋆Assoc _ _ _)} refl refl)
      ∙ pullbackArrowUnique f1≡g1 f2≡g2
    -- TODO: this is a natural iso proving that Yoneda preserves
    -- pullbacks.
    isPullback→ΣIso : ∀ Γ (f : C [ Γ , l ])
      → Iso (fiber (C._⋆ pbPr₁) f)
            (fiber (C._⋆ s₂) (f C.⋆ s₁))
    isPullback→ΣIso Γ f .fun (g , gπ₁≡f) = (g C.⋆ pbPr₂) ,
      C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ sym $ pbCommutes ⟩
      ∙ sym (C.⋆Assoc _ _ _)
      ∙ C.⟨ gπ₁≡f ⟩⋆⟨ refl ⟩
    isPullback→ΣIso Γ f .inv (h , hs₂≡fs₁) = (pullbackArrow f h (sym $ hs₂≡fs₁))
      , (sym $ pullbackArrowPr₁ C pb f h (sym $  hs₂≡fs₁))
    isPullback→ΣIso Γ f .sec (h , hs₂≡fs₁) = ΣPathPProp (λ _ → C.isSetHom _ _) $
      (sym $ pullbackArrowPr₂ C pb f h (sym $  hs₂≡fs₁))
    isPullback→ΣIso Γ f .ret (g , gπ₁≡f) = ΣPathPProp (λ _ → C.isSetHom _ _) $
      pullbackArrowUnique (sym gπ₁≡f) refl
