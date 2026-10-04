{-# OPTIONS --lossy-unification #-}
-- For a monoidal category (V, I), the hom functor
--   V[I, -] : V → Set
-- is lax monoidal, with Set given its cartesian monoidal structure
-- (see `Monoidal.Instances.Sets`).  Lax structure:
--   ε  : *     ↦ V.id {I}
--   μ  : (f, g) ↦ η⁻¹⟨I⟩ ⋆ (f ⊗ g)             (f : I → x, g : I → y)
module Cubical.Categories.Monoidal.Functor.Instances.Set.HomFromUnit where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More using (NatIsoAt)
open import Cubical.Categories.Instances.BinProduct using (CatIso×)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Cartesian.More
  using (CartesianMonoidalCategory)
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.Instances.Sets using (SETCartMon)
open import Cubical.Categories.Monoidal.Properties
  using (ρ⟨unit⟩≡η⟨unit⟩; triangle')

private variable ℓV ℓV' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso
open LaxMonoidalStr
open LaxMonoidalFunctor

module _ (V : MonoidalCategory ℓV ℓV') where
  private
    module V = MonoidalCategory V

  SetMon : MonoidalCategory (ℓ-suc ℓV') ℓV'
  SetMon = CartesianMonoidalCategory.asMonoidal (SETCartMon {ℓV'})

  private module S = MonoidalCategory SetMon

  HomFromUnit : Functor V.C (SET ℓV')
  HomFromUnit .F-ob x = V.C [ V.unit , x ] , V.C .isSetHom
  HomFromUnit .F-hom f g = g V.⋆ f
  HomFromUnit .F-id = funExt λ g → V.⋆IdR g
  HomFromUnit .F-seq f g = funExt λ h → sym (V.⋆Assoc h f g)

  -- The two canonical maps `I ⊗ I → (I ⊗ I) ⊗ I` agree.  Follows from
  -- triangle at (I, I) together with `ρ⟨I⟩ ≡ η⟨I⟩`: both composites
  -- with `(η⟨I⟩ ⊗ id)` on the left reduce to the identity, so by
  -- cancellation they are equal.
  private
    η⁻¹⊗≡id⊗η⁻¹⋆α :
        (V.η⁻¹⟨ V.unit ⟩ V.⊗ₕ V.id {V.unit})
      ≡ (V.id {V.unit} V.⊗ₕ V.η⁻¹⟨ V.unit ⟩) V.⋆
          V.α⟨ V.unit , V.unit , V.unit ⟩
    η⁻¹⊗≡id⊗η⁻¹⋆α = ⋆CancelL η⊗id-Iso (lhsEqId ∙ sym rhsEqId)
      where
      η⊗id-Iso :
        CatIso V.C ((V.unit V.⊗ V.unit) V.⊗ V.unit) (V.unit V.⊗ V.unit)
      η⊗id-Iso = F-Iso {F = V.─⊗─}
        (CatIso× V.C V.C (NatIsoAt V.η V.unit) idCatIso)

      lhsEqId :
          (V.η⟨ V.unit ⟩ V.⊗ₕ V.id {V.unit}) V.⋆
            (V.η⁻¹⟨ V.unit ⟩ V.⊗ₕ V.id {V.unit})
        ≡ V.id {(V.unit V.⊗ V.unit) V.⊗ V.unit}
      lhsEqId =
          sym (V.─⊗─ .F-seq (V.η⟨ V.unit ⟩ , V.id {V.unit})
                            (V.η⁻¹⟨ V.unit ⟩ , V.id {V.unit}))
        ∙ cong₂ V._⊗ₕ_ (V.η .nIso V.unit .ret) (V.⋆IdL (V.id {V.unit}))
        ∙ V.─⊗─ .F-id

      tri :
          (V.η⟨ V.unit ⟩ V.⊗ₕ V.id {V.unit})
        ≡ V.α⁻¹⟨ V.unit , V.unit , V.unit ⟩ V.⋆
            (V.id {V.unit} V.⊗ₕ V.η⟨ V.unit ⟩)
      tri = cong (V._⊗ₕ V.id {V.unit}) (sym (ρ⟨unit⟩≡η⟨unit⟩ V))
          ∙ triangle' V V.unit V.unit

      rhsEqId :
          (V.η⟨ V.unit ⟩ V.⊗ₕ V.id {V.unit}) V.⋆
            ((V.id {V.unit} V.⊗ₕ V.η⁻¹⟨ V.unit ⟩) V.⋆
              V.α⟨ V.unit , V.unit , V.unit ⟩)
        ≡ V.id {(V.unit V.⊗ V.unit) V.⊗ V.unit}
      rhsEqId =
          cong (V._⋆ ((V.id {V.unit} V.⊗ₕ V.η⁻¹⟨ V.unit ⟩) V.⋆
                      V.α⟨ V.unit , V.unit , V.unit ⟩)) tri
        ∙ V.⋆Assoc _ _ _
        ∙ cong (V.α⁻¹⟨ V.unit , V.unit , V.unit ⟩ V.⋆_)
            (  sym (V.⋆Assoc _ _ _)
            ∙ cong (V._⋆ V.α⟨ V.unit , V.unit , V.unit ⟩)
                (  sym (V.─⊗─ .F-seq (V.id {V.unit} , V.η⟨ V.unit ⟩)
                                     (V.id {V.unit} , V.η⁻¹⟨ V.unit ⟩))
                ∙ cong₂ V._⊗ₕ_ (V.⋆IdL (V.id {V.unit}))
                               (V.η .nIso V.unit .ret)
                ∙ V.─⊗─ .F-id)
            ∙ V.⋆IdL _)
        ∙ V.α .nIso (V.unit , V.unit , V.unit) .sec

  HomFromUnit-lax : LaxMonoidalStr V SetMon HomFromUnit
  HomFromUnit-lax .ε _ = V.id
  HomFromUnit-lax .μ .N-ob (x , y) (f , g) =
    V.η⁻¹⟨ V.unit ⟩ V.⋆ (f V.⊗ₕ g)
  HomFromUnit-lax .μ .N-hom {x = (x , y)}{y = (x' , y')} (f , g) =
    funExt λ (a , b) →
      V.η⁻¹⟨ V.unit ⟩ V.⋆ ((a V.⋆ f) V.⊗ₕ (b V.⋆ g))
        ≡⟨ cong (V.η⁻¹⟨ V.unit ⟩ V.⋆_) (V.─⊗─ .F-seq _ _) ⟩
      V.η⁻¹⟨ V.unit ⟩ V.⋆ ((a V.⊗ₕ b) V.⋆ (f V.⊗ₕ g))
        ≡⟨ sym (V.⋆Assoc _ _ _) ⟩
      (V.η⁻¹⟨ V.unit ⟩ V.⋆ (a V.⊗ₕ b)) V.⋆ (f V.⊗ₕ g) ∎
  HomFromUnit-lax .αμ-law x y z = funExt λ (a , b , c) →
      V.η⁻¹⟨ V.unit ⟩ V.⋆
        ((V.η⁻¹⟨ V.unit ⟩ V.⋆ (a V.⊗ₕ b)) V.⊗ₕ c)
        ≡⟨ cong (V.η⁻¹⟨ V.unit ⟩ V.⋆_)
            (  cong (λ q → (V.η⁻¹⟨ V.unit ⟩ V.⋆ (a V.⊗ₕ b)) V.⊗ₕ q)
                 (sym (V.⋆IdL c))
            ∙ V.─⊗─ .F-seq _ _) ⟩
      V.η⁻¹⟨ V.unit ⟩ V.⋆
        ((V.η⁻¹⟨ V.unit ⟩ V.⊗ₕ V.id {V.unit}) V.⋆
          ((a V.⊗ₕ b) V.⊗ₕ c))
        ≡⟨ sym (V.⋆Assoc _ _ _) ⟩
      (V.η⁻¹⟨ V.unit ⟩ V.⋆ (V.η⁻¹⟨ V.unit ⟩ V.⊗ₕ V.id {V.unit}))
        V.⋆ ((a V.⊗ₕ b) V.⊗ₕ c)
        ≡⟨ cong (V._⋆ ((a V.⊗ₕ b) V.⊗ₕ c))
            (cong (V.η⁻¹⟨ V.unit ⟩ V.⋆_) η⁻¹⊗≡id⊗η⁻¹⋆α) ⟩
      (V.η⁻¹⟨ V.unit ⟩ V.⋆
        ((V.id {V.unit} V.⊗ₕ V.η⁻¹⟨ V.unit ⟩) V.⋆
          V.α⟨ V.unit , V.unit , V.unit ⟩))
        V.⋆ ((a V.⊗ₕ b) V.⊗ₕ c)
        ≡⟨ cong (V._⋆ ((a V.⊗ₕ b) V.⊗ₕ c)) (sym (V.⋆Assoc _ _ _)) ⟩
      ((V.η⁻¹⟨ V.unit ⟩ V.⋆ (V.id {V.unit} V.⊗ₕ V.η⁻¹⟨ V.unit ⟩))
        V.⋆ V.α⟨ V.unit , V.unit , V.unit ⟩)
        V.⋆ ((a V.⊗ₕ b) V.⊗ₕ c)
        ≡⟨ V.⋆Assoc _ _ _ ⟩
      (V.η⁻¹⟨ V.unit ⟩ V.⋆ (V.id {V.unit} V.⊗ₕ V.η⁻¹⟨ V.unit ⟩))
        V.⋆ (V.α⟨ V.unit , V.unit , V.unit ⟩ V.⋆ ((a V.⊗ₕ b) V.⊗ₕ c))
        ≡⟨ cong ((V.η⁻¹⟨ V.unit ⟩ V.⋆
                   (V.id {V.unit} V.⊗ₕ V.η⁻¹⟨ V.unit ⟩)) V.⋆_)
            (sym (V.α .trans .N-hom (a , b , c))) ⟩
      (V.η⁻¹⟨ V.unit ⟩ V.⋆ (V.id {V.unit} V.⊗ₕ V.η⁻¹⟨ V.unit ⟩))
        V.⋆ ((a V.⊗ₕ (b V.⊗ₕ c)) V.⋆ V.α⟨ x , y , z ⟩)
        ≡⟨ sym (V.⋆Assoc _ _ _) ⟩
      ((V.η⁻¹⟨ V.unit ⟩ V.⋆ (V.id {V.unit} V.⊗ₕ V.η⁻¹⟨ V.unit ⟩))
        V.⋆ (a V.⊗ₕ (b V.⊗ₕ c)))
        V.⋆ V.α⟨ x , y , z ⟩
        ≡⟨ cong (V._⋆ V.α⟨ x , y , z ⟩) (V.⋆Assoc _ _ _) ⟩
      (V.η⁻¹⟨ V.unit ⟩ V.⋆
        ((V.id {V.unit} V.⊗ₕ V.η⁻¹⟨ V.unit ⟩) V.⋆
          (a V.⊗ₕ (b V.⊗ₕ c))))
        V.⋆ V.α⟨ x , y , z ⟩
        ≡⟨ cong (λ q → (V.η⁻¹⟨ V.unit ⟩ V.⋆ q) V.⋆ V.α⟨ x , y , z ⟩)
            (sym
              (  cong (λ q → q V.⊗ₕ (V.η⁻¹⟨ V.unit ⟩ V.⋆ (b V.⊗ₕ c)))
                   (sym (V.⋆IdL a))
              ∙ V.─⊗─ .F-seq _ _)) ⟩
      (V.η⁻¹⟨ V.unit ⟩ V.⋆ (a V.⊗ₕ (V.η⁻¹⟨ V.unit ⟩ V.⋆ (b V.⊗ₕ c))))
        V.⋆ V.α⟨ x , y , z ⟩ ∎
  HomFromUnit-lax .ηε-law x = funExt λ (_ , h) →
      (V.η⁻¹⟨ V.unit ⟩ V.⋆ (V.id {V.unit} V.⊗ₕ h)) V.⋆ V.η⟨ x ⟩
        ≡⟨ V.⋆Assoc _ _ _ ⟩
      V.η⁻¹⟨ V.unit ⟩ V.⋆ ((V.id {V.unit} V.⊗ₕ h) V.⋆ V.η⟨ x ⟩)
        ≡⟨ cong (V.η⁻¹⟨ V.unit ⟩ V.⋆_) (V.η .trans .N-hom h) ⟩
      V.η⁻¹⟨ V.unit ⟩ V.⋆ (V.η⟨ V.unit ⟩ V.⋆ h)
        ≡⟨ sym (V.⋆Assoc _ _ _) ⟩
      (V.η⁻¹⟨ V.unit ⟩ V.⋆ V.η⟨ V.unit ⟩) V.⋆ h
        ≡⟨ cong (V._⋆ h) (V.η .nIso V.unit .sec) ⟩
      V.id V.⋆ h
        ≡⟨ V.⋆IdL h ⟩
      h ∎
  HomFromUnit-lax .ρε-law x = funExt λ (h , _) →
      (V.η⁻¹⟨ V.unit ⟩ V.⋆ (h V.⊗ₕ V.id {V.unit})) V.⋆ V.ρ⟨ x ⟩
        ≡⟨ V.⋆Assoc _ _ _ ⟩
      V.η⁻¹⟨ V.unit ⟩ V.⋆ ((h V.⊗ₕ V.id {V.unit}) V.⋆ V.ρ⟨ x ⟩)
        ≡⟨ cong (V.η⁻¹⟨ V.unit ⟩ V.⋆_) (V.ρ .trans .N-hom h) ⟩
      V.η⁻¹⟨ V.unit ⟩ V.⋆ (V.ρ⟨ V.unit ⟩ V.⋆ h)
        ≡⟨ cong (V.η⁻¹⟨ V.unit ⟩ V.⋆_)
            (cong (V._⋆ h) (ρ⟨unit⟩≡η⟨unit⟩ V)) ⟩
      V.η⁻¹⟨ V.unit ⟩ V.⋆ (V.η⟨ V.unit ⟩ V.⋆ h)
        ≡⟨ sym (V.⋆Assoc _ _ _) ⟩
      (V.η⁻¹⟨ V.unit ⟩ V.⋆ V.η⟨ V.unit ⟩) V.⋆ h
        ≡⟨ cong (V._⋆ h) (V.η .nIso V.unit .sec) ⟩
      V.id V.⋆ h
        ≡⟨ V.⋆IdL h ⟩
      h ∎

  HomFromUnitLax : LaxMonoidalFunctor V SetMon
  HomFromUnitLax .F = HomFromUnit
  HomFromUnitLax .laxmonstr = HomFromUnit-lax
