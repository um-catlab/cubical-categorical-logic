{- Lax and Strong Monoidal Functors -}
{-# OPTIONS --safe #-}

module Cubical.Categories.Monoidal.Functor where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
open Category
open Functor
open isIso
module _ (M : MonoidalCategory ℓC ℓC') (N : MonoidalCategory ℓD ℓD') where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N

  module _ (F : Functor M.C N.C) where
    record LaxMonoidalStr : Type (ℓ-max ℓC (ℓ-max ℓC' ℓD'))
      where
      field
        ε : N.C [ N.unit , F ⟅ M.unit ⟆ ]
        -- N.C [ F x ⊗ F y , F (x ⊗ y) ]
        μ : N.─⊗─ ∘F (F ×F F) ⇒ F ∘F M.─⊗─

      μ⟨_,_⟩ : ∀ x y → N.C [ (F ⟅ x ⟆) N.⊗ (F ⟅ y ⟆) , F ⟅ x M.⊗ y ⟆ ]
      μ⟨ x , y ⟩ = μ ⟦ x , y ⟧

      field
        αμ-law : ∀ (x y z : M.C .ob) →
          Path (N.C [ (F ⟅ x ⟆) N.⊗ ((F ⟅ y ⟆) N.⊗ (F ⟅ z ⟆)) , F ⟅ (x M.⊗ y) M.⊗ z ⟆ ])
            (N.α⟨ _ , _ , _ ⟩ ⋆⟨ N.C ⟩ (μ⟨ x , y ⟩ N.⊗ₕ N.id) ⋆⟨ N.C ⟩ μ⟨ _ , z ⟩)
            (N.id N.⊗ₕ μ⟨ y , z ⟩ ⋆⟨ N.C ⟩ μ⟨ x , _ ⟩ ⋆⟨ N.C ⟩ F ⟪ M.α⟨ x , y , z ⟩ ⟫)
        ηε-law : ∀ x →
          Path (N.C [ N.unit N.⊗ (F ⟅ x ⟆) , F ⟅ x ⟆ ])
            (ε N.⊗ₕ N.id ⋆⟨ N.C ⟩ μ⟨ M.unit , x ⟩ ⋆⟨ N.C ⟩ F ⟪ M.η⟨ x ⟩ ⟫)
            N.η⟨ F ⟅ x ⟆ ⟩
      -- α⁻μ-law
      η⁻ε-law : ∀ x →
        N.η⁻¹⟨ F ⟅ x ⟆ ⟩ ⋆⟨ N.C ⟩ (ε N.⊗ₕ N.id) ⋆⟨ N.C ⟩ μ⟨ _ , _ ⟩
        ≡ F ⟪ M.η⁻¹⟨ x ⟩ ⟫
      η⁻ε-law x = ⋆CancelR (F-Iso {F = F} ((NatIsoAt M.η _)))
        (((N.⋆Assoc _ _ _) ∙ N.⋆Assoc _ _ _
        ∙ cong₂ N._⋆_ refl (sym (N.⋆Assoc _ _ _) ∙ ηε-law x)
        ∙ NatIsoAt N.η _ .snd .sec)
        ∙ sym (F .F-id)
        ∙ cong (F .F-hom) (sym (NatIsoAt M.η _ .snd .sec))
        ∙ F .F-seq _ _)
    -- equivalent to LaxMonoidal stuff with op but we'll define it
    -- explicitly for ergonomics
    record OpLaxMonoidalStr : Type (ℓ-max ℓC (ℓ-max ℓC' ℓD')) where
      field
        ε⁻ : N.C [ F ⟅ M.unit ⟆ , N.unit ]
        μ⁻ : F ∘F M.─⊗─ ⇒ N.─⊗─ ∘F (F ×F F)

      μ⁻⟨_,_⟩ : ∀ x y → N.C [ F ⟅ x M.⊗ y ⟆ , (F ⟅ x ⟆) N.⊗ (F ⟅ y ⟆) ]
      μ⁻⟨ x , y ⟩ = μ⁻ ⟦ x , y ⟧

      field
        α⁻μ⁻-law : ∀ (x y z : M.C .ob) →
            (μ⁻⟨ _ , z ⟩ ⋆⟨ N.C ⟩ (μ⁻⟨ x , y ⟩ N.⊗ₕ N.id) ⋆⟨ N.C ⟩ N.α⁻¹⟨ _ , _ , _ ⟩)
            ≡
            (F ⟪ M.α⁻¹⟨ x , y , z ⟩ ⟫ ⋆⟨ N.C ⟩ μ⁻⟨ x , _ ⟩ ⋆⟨ N.C ⟩ N.id N.⊗ₕ μ⁻⟨ y , z ⟩)

        η⁻-law : ∀ x →
            (F ⟪ M.η⁻¹⟨ x ⟩ ⟫ ⋆⟨ N.C ⟩ μ⁻⟨ M.unit , x ⟩ ⋆⟨ N.C ⟩ ε⁻ N.⊗ₕ N.id)
            ≡ N.η⁻¹⟨ F ⟅ x ⟆ ⟩


    -- TODO: α-law⁻ , α⁻¹-law, η⁻¹-law, ρ-law ρ⁻¹-law all derivable

    record StrongMonoidalStr : Type ((ℓ-max ℓC (ℓ-max ℓC' ℓD'))) where
      field
        laxmonstr : LaxMonoidalStr
      open LaxMonoidalStr laxmonstr public
      field
        ε-isIso : isIso N.C ε
        μ-isIso : ∀ x → isIso N.C (μ ⟦ x ⟧)

      ε-Iso : CatIso N.C N.unit (F ⟅ M.unit ⟆)
      ε-Iso = ε , ε-isIso

      μ-Iso :  N.─⊗─ ∘F (F ×F F) ≅ᶜ F ∘F M.─⊗─
      μ-Iso = record { trans = μ ; nIso = μ-isIso }

      -- oplaxmonstr : OpLaxMonoidalStr
      -- oplaxmonstr .OpLaxMonoidalStr.ε⁻ = ε-isIso .isIso.inv
      -- oplaxmonstr .OpLaxMonoidalStr.μ⁻ = symNatIso μ-Iso .NatIso.trans
      -- oplaxmonstr .OpLaxMonoidalStr.α⁻-law x y z = {!α-law x y z!}
      -- oplaxmonstr .OpLaxMonoidalStr.η⁻-law = {!!}

      -- open OpLaxMonoidalStr oplaxmonstr public

  record LaxMonoidalFunctor : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      F : Functor M.C N.C
      laxmonstr : LaxMonoidalStr F
    open Functor F public
    open LaxMonoidalStr laxmonstr public

  record OplaxMonoidalFunctor : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      F : Functor M.C N.C
      oplaxmonstr : OpLaxMonoidalStr F
    open Functor F public
    open OpLaxMonoidalStr oplaxmonstr public

  record StrongMonoidalFunctor : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      F : Functor M.C N.C
      strmonstr : StrongMonoidalStr F
    open Functor F public
    open StrongMonoidalStr strmonstr public

module _ {M : MonoidalCategory ℓC ℓC'} where
  open LaxMonoidalStr
  open Functor
  private
    module M = MonoidalCategory M

  IdLaxStr : LaxMonoidalStr M M (Id {C = M.C})
  IdLaxStr .ε = M.id
  IdLaxStr .μ = natTrans (λ _ → M.id) (λ f → M.⋆IdR _ ∙ sym (M.⋆IdL _))
  IdLaxStr .αμ-law x y z =
    M.⋆IdR _
    ∙ (λ i → M.α⟨ _ , _ , _ ⟩ M.⋆ (M.─⊗─ .F-id i))
    ∙ M.⋆IdR _
    ∙ sym (M.⋆IdL _)
    ∙ (λ i → (M.─⊗─ .F-id (~ i)) M.⋆ M.α⟨ _ , _ , _ ⟩)
    ∙ cong₂ M._⋆_ (sym (M.⋆IdR _)) refl
  IdLaxStr .ηε-law x =
    cong₂ M._⋆_ (M.⋆IdR _) refl
    ∙ cong₂ M._⋆_ (M.─⊗─ .F-id) refl
    ∙ M.⋆IdL _

  IdStrStr : StrongMonoidalStr M M (Id {C = M.C})
  IdStrStr .StrongMonoidalStr.laxmonstr = IdLaxStr
  IdStrStr .StrongMonoidalStr.ε-isIso = idCatIso .snd
  IdStrStr .StrongMonoidalStr.μ-isIso = λ _ → idCatIso .snd

  IdLax : LaxMonoidalFunctor M M
  IdLax .LaxMonoidalFunctor.F = Id
  IdLax .LaxMonoidalFunctor.laxmonstr = IdLaxStr

  IdStr : StrongMonoidalFunctor M M
  IdStr .StrongMonoidalFunctor.F = Id
  IdStr .StrongMonoidalFunctor.strmonstr = IdStrStr
