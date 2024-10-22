{-# OPTIONS --safe #-}

module Cubical.Categories.Monoidal.Properties where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.HLevels
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Dual

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
open Category
open Functor
open isIso
open NatTrans
open NatIso

record MonoidalPreorder ℓC ℓC' : Type (ℓ-suc (ℓ-max ℓC ℓC')) where
  field
    C : Category ℓC ℓC'
    isPropHom : ∀ {x y} → isProp (C [ x , y ])
    unit : C .ob
    ─⊗─ : Functor (C ×C C) C
  _⊗_ : C .ob → C .ob → C .ob
  x ⊗ y = ─⊗─ .F-ob (x , y)
  field
    α⟨_,_,_⟩ : (x y z : C .ob) → C [ x ⊗ (y ⊗ z) , (x ⊗ y) ⊗ z ]
    α⁻¹⟨_,_,_⟩ : (x y z : C .ob) → C [ (x ⊗ y) ⊗ z , x ⊗ (y ⊗ z) ]
    η⟨_⟩ : (x : C .ob) → C [ unit ⊗ x , x ]
    η⁻¹⟨_⟩ : (x : C .ob) → C [ x , unit ⊗ x ]
    ρ⟨_⟩ : (x : C .ob) → C [ x ⊗ unit , x ]
    ρ⁻¹⟨_⟩ : (x : C .ob) → C [ x , x ⊗ unit ]

module _ (M : MonoidalPreorder ℓC ℓC') where
  private
    module M = MonoidalPreorder M
    private
      TS : TensorStr M.C
      TS = record { ─⊗─ = M.─⊗─ ; unit = M.unit }
  MonoidalPreorder→MonoidalCategory : MonoidalCategory ℓC ℓC'
  MonoidalPreorder→MonoidalCategory .MonoidalCategory.C = M.C
  MonoidalPreorder→MonoidalCategory .MonoidalCategory.monstr .MonoidalStr.tenstr
    = TS
  MonoidalPreorder→MonoidalCategory .MonoidalCategory.monstr .MonoidalStr.α =
    mkNatIso M.C M.isPropHom (λ _ → M.α⟨ _ , _ , _ ⟩) (λ _ → M.α⁻¹⟨ _ , _ , _ ⟩)
  MonoidalPreorder→MonoidalCategory .MonoidalCategory.monstr .MonoidalStr.η =
    mkNatIso M.C M.isPropHom (λ _ → M.η⟨ _ ⟩) (λ _ → M.η⁻¹⟨ _ ⟩)
  MonoidalPreorder→MonoidalCategory .MonoidalCategory.monstr .MonoidalStr.ρ =
    mkNatIso M.C M.isPropHom (λ _ → M.ρ⟨ _ ⟩) (λ _ → M.ρ⁻¹⟨ _ ⟩)
  MonoidalPreorder→MonoidalCategory .MonoidalCategory.monstr
    .MonoidalStr.pentagon _ _ _ _ = M.isPropHom _ _
  MonoidalPreorder→MonoidalCategory .MonoidalCategory.monstr
    .MonoidalStr.triangle _ _ = M.isPropHom _ _
module _ (M : MonoidalCategory ℓC ℓC') where
  private
    module M = MonoidalCategory M
    module M^co = MonoidalCategory (M ^co)

  ⊗id-cancel : ∀ {x y : M.ob}
    → {f g : M.C [ x , y ]}
    → (f M.⊗ₕ M.id {M.unit}) ≡ (g M.⊗ₕ M.id)
    → f ≡ g
  ⊗id-cancel p =
    ⋆CancelL (NatIsoAt M.ρ _)
      (sym (M.ρ .trans .N-hom _)
      ∙ cong₂ M._⋆_ p refl
      ∙ M.ρ .trans .N-hom _)

  id⊗-cancel : ∀ {x y : M.ob}
    → {f g : M.C [ x , y ]}
    → (M.id {M.unit} M.⊗ₕ f) ≡ (M.id M.⊗ₕ g)
    → f ≡ g
  id⊗-cancel p = ⋆CancelL (NatIsoAt M.η _)
    (sym (M.η .trans .N-hom _)
      ∙ cong₂ M._⋆_ p refl
      ∙ M.η .trans .N-hom _)

  triangle' : ∀ x y →
    (M.ρ⟨ x ⟩ M.⊗ₕ M.id) ≡ (M.α⁻¹⟨ x , M.unit , y ⟩ M.⋆ (M.id M.⊗ₕ M.η⟨ y ⟩))
  triangle' x y = ⋆InvLMove (NatIsoAt M.α _) (M.triangle x y)

  opaque
    pentagon' : ∀ w x y z
      → (M.α⟨ (w M.⊗ x) , y , z ⟩ M.⋆ (M.α⁻¹⟨ w , x , y ⟩ M.⊗ₕ M.id {z}))
        M.⋆ M.α⁻¹⟨ w , (x M.⊗ y) , z ⟩
       ≡ (M.α⁻¹⟨ w , x , (y M.⊗ z) ⟩ M.⋆ (M.id M.⊗ₕ M.α⟨ x , y , z ⟩))
    pentagon' w x y z =
      ⋆InvLMove (NatIsoAt M.α _)
        (sym (M.⋆Assoc _ _ _)
        ∙ sym (⋆InvRMove (NatIsoAt M.α _)
        (⋆InvRMove
          (F-Iso {F = M.─⊗─} (CatIso× M.C M.C (NatIsoAt M.α _) idCatIso))
          (M.⋆Assoc _ _ _ ∙ M.pentagon w x y z)
         ∙ M.⋆Assoc _ _ _)))

    ρ⟨⊗⟩ : ∀ {x y}
      → (M.α⟨ x , y , M.unit ⟩ M.⋆ (M.ρ⟨ x M.⊗ y ⟩)) ≡ (M.id {x} M.⊗ₕ M.ρ⟨ y ⟩ )
    ρ⟨⊗⟩ {x}{y} = ⊗id-cancel
      (⋆CancelL (NatIsoAt M.α _)
        (cong₂ M._⋆_ refl
          (cong₂ M._⊗ₕ_ refl
            (sym (M.⋆IdL _)) ∙ M.─⊗─ .F-seq _ _)
          ∙ sym (M.⋆Assoc _ _ _)
          ∙ cong₂ M._⋆_
            (⋆CancelL
              (F-Iso {F = M.─⊗─} (CatIso× M.C M.C idCatIso (NatIsoAt M.α _)))
              (M.pentagon _ _ _ _
              ∙ sym (M.⋆IdL _)
              ∙ cong₂ M._⋆_
                (sym (F-Iso {F = M.─⊗─}
                            (CatIso× M.C M.C idCatIso (NatIsoAt M.α _))
                            .snd .ret))
                refl
              ∙ M.⋆Assoc _ _ _))
              refl
        ∙ M.⋆Assoc _ _ _
        ∙ cong₂ M._⋆_ refl
          (M.⋆Assoc _ _ _
          ∙ cong₂ M._⋆_ refl
            (M.triangle _ _
            ∙ cong₂ M._⊗ₕ_ (sym (M.─⊗─ .F-id)) refl)
          ∙ sym (M.α .trans .N-hom _))
        ∙ sym (M.⋆Assoc _ _ _)
        ∙ cong₂ M._⋆_
          (sym (M.─⊗─ .F-seq _ _) ∙ cong₂ M._⊗ₕ_ (M.⋆IdL _) refl)
          refl
        ∙ cong₂ M._⋆_
          (cong₂ M._⊗ₕ_ refl
            (⋆CancelL (NatIsoAt M.α _)
              (sym (⋆InvLMove (invIso (NatIsoAt M.α _)) refl)
              ∙ sym (M.triangle _ _))))
            refl
        ∙ M.α .trans .N-hom _ ))
  opaque
    ρ⟨unit⟩≡η⟨unit⟩ : M.ρ⟨ M.unit ⟩ ≡ M.η⟨ M.unit ⟩
    ρ⟨unit⟩≡η⟨unit⟩ = id⊗-cancel
      (sym ρ⟨⊗⟩
      ∙ cong₂ M._⋆_ refl
        (⋆CancelR (NatIsoAt M.ρ _)
          (sym (M.ρ .trans .N-hom (M.ρ⟨ M.unit ⟩))))
      ∙ M.triangle _ _)

module _ (M : MonoidalCategory ℓC ℓC') where
  private
    module M = MonoidalCategory M
    module M^co = MonoidalCategory (M ^co)
  η⟨⊗⟩ : ∀ x y →
    (M.α⟨ M.unit , x , y ⟩ M.⋆ (M.η⟨ x ⟩ M.⊗ₕ M.id {y}))
    ≡ M.η⟨ x M.⊗ y ⟩
  η⟨⊗⟩ x y = sym (⋆InvLMove (invIso (NatIsoAt M.α _))
    (ρ⟨⊗⟩ (M ^co)))

