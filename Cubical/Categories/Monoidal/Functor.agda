{- Lax and Strong Monoidal Functors -}
{-# OPTIONS --safe #-}

module Cubical.Categories.Monoidal.Functor where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
open Category
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
        assoc-law : ∀ (x y z : M.C .ob) →
          Path (N.C [ (F ⟅ x ⟆) N.⊗ ((F ⟅ y ⟆) N.⊗ (F ⟅ z ⟆)) , F ⟅ (x M.⊗ y) M.⊗ z ⟆ ])
            (N.α⟨ _ , _ , _ ⟩ ⋆⟨ N.C ⟩ (μ⟨ x , y ⟩ N.⊗ₕ N.id) ⋆⟨ N.C ⟩ μ⟨ _ , z ⟩)
            (N.id N.⊗ₕ μ⟨ y , z ⟩ ⋆⟨ N.C ⟩ μ⟨ x , _ ⟩ ⋆⟨ N.C ⟩ F ⟪ M.α⟨ x , y , z ⟩ ⟫)
        unit-law : ∀ x →
          Path (N.C [ N.unit N.⊗ (F ⟅ x ⟆) , F ⟅ x ⟆ ])
            (ε N.⊗ₕ N.id ⋆⟨ N.C ⟩ μ⟨ M.unit , x ⟩ ⋆⟨ N.C ⟩ F ⟪ M.η⟨ x ⟩ ⟫)
            N.η⟨ F ⟅ x ⟆ ⟩

    record StrongMonoidalStr : Type ((ℓ-max ℓC (ℓ-max ℓC' ℓD'))) where
      field
        laxmonstr : LaxMonoidalStr
      open LaxMonoidalStr laxmonstr public
      field
        ε-iso : isIso N.C ε
        μ-iso : ∀ x → isIso N.C (μ ⟦ x ⟧)

  record LaxMonoidalFunctor : Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
    field
      F : Functor M.C N.C
      laxmonstr : LaxMonoidalStr F
    open Functor F public
    open LaxMonoidalStr laxmonstr public

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
  IdLaxStr .assoc-law x y z =
    M.⋆IdR _
    ∙ (λ i → M.α⟨ _ , _ , _ ⟩ M.⋆ (M.─⊗─ .F-id i))
    ∙ M.⋆IdR _
    ∙ sym (M.⋆IdL _)
    ∙ (λ i → (M.─⊗─ .F-id (~ i)) M.⋆ M.α⟨ _ , _ , _ ⟩)
    ∙ cong₂ M._⋆_ (sym (M.⋆IdR _)) refl
  IdLaxStr .unit-law x =
    cong₂ M._⋆_ (M.⋆IdR _) refl
    ∙ cong₂ M._⋆_ (M.─⊗─ .F-id) refl
    ∙ M.⋆IdL _

  IdStrStr : StrongMonoidalStr M M (Id {C = M.C})
  IdStrStr .StrongMonoidalStr.laxmonstr = IdLaxStr
  IdStrStr .StrongMonoidalStr.ε-iso = idCatIso .snd 
  IdStrStr .StrongMonoidalStr.μ-iso = λ _ → idCatIso .snd

  IdLax : LaxMonoidalFunctor M M
  IdLax .LaxMonoidalFunctor.F = Id
  IdLax .LaxMonoidalFunctor.laxmonstr = IdLaxStr

  IdStr : StrongMonoidalFunctor M M
  IdStr .StrongMonoidalFunctor.F = Id
  IdStr .StrongMonoidalFunctor.strmonstr = IdStrStr
