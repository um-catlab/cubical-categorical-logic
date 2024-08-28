{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Fibration.Base
import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Instances.Sets.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Category
open UniversalElement
open Functorᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (isFib : AllCartesianOvers Cᴰ) {- for typechecking performance -}
  (vps : VerticalBinProducts Cᴰ)
  where
  open CartesianOver
  open Cubical.Categories.Displayed.Reasoning Cᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
  module _ {c : C .ob}
    (cᴰ cᴰ' : Cᴰ.ob[ c ]) where
    VerticalExponentialsAt : (cᴰ'' : Cᴰ.ob[ c ]) → Type _
    VerticalExponentialsAt cᴰ'' = UniversalElementᴰ Cᴰ Pᴰ idue
      where
      -- TODO: this is already in the library, I just don't want to find it right now
      idue : UniversalElement C (C [-, c ])
      idue .vertex = c
      idue .element = C .id
      idue .universal c' .equiv-proof f = uniqueExists
        f (C .⋆IdR _) (λ _ → C .isSetHom _ _) (λ _ p → sym p ∙ C .⋆IdR _)
      module _ {c' : C .ob } (c'ᴰ : Cᴰ.ob[ c' ])(f : C [ c' , c ]) where
        module ∧ = VerticalBinProductsAtNotation (vps (c'ᴰ , isFib cᴰ f .f*cᴰ'))
      Pᴰ : Presheafᴰ Cᴰ (C [-, c ]) _
      Pᴰ .F-obᴰ {x = c'} c'ᴰ f = Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ] , Cᴰ.isSetHomᴰ
      Pᴰ .F-homᴰ {x = c'} {y = c''} {f = g} {xᴰ = c'ᴰ} {yᴰ = c''ᴰ} gᴰ f fᴰ =
        ∧.⟨_,_⟩ c'ᴰ f
          (reind (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (∧.π₁ c''ᴰ (g ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ gᴰ))
          (reind (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (∧.π₂ c''ᴰ (g ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ isFib cᴰ f .isCartesian _ g (isFib cᴰ (g ⋆⟨ C ⟩ f) .π) .fst .fst))
        Cᴰ.⋆ᴰ fᴰ
      Pᴰ .F-idᴰ {x = c'} {xᴰ = c'ᴰ} = funExt (λ f → funExt (λ fᴰ → goal f fᴰ {- compPathP' (congP (λ i a → {!!} Cᴰ.⋆ᴰ fᴰ) {!!}) (Cᴰ.⋆IdLᴰ fᴰ) -} )) --Cᴰ.⋆IdLᴰ fᴰ
        where
        left : ∀ f (fᴰ : Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ]) →
          (∧.⟨_,_⟩ c'ᴰ f
            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
              (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))
            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
              (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
                isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ')
                (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst)))
          ≡ {!Cᴰ.idᴰ!}
        left f fᴰ = {!!}
        subgoal : ∀ f (fᴰ : Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ]) →
          PathP (λ i → Cᴰ.Hom[ C .id ][ ∧.vert c'ᴰ (C .⋆IdL f i) , ∧.vert c'ᴰ f ])
            {!!}
            --(∧.⟨_,_⟩ c'ᴰ f
            -- (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
            --  (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))
            -- (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
            --  (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
            --   isFib cᴰ f .isCartesian (isFib cᴰ (seq' C (C .id) f) .f*cᴰ')
            --   (C .id) (isFib cᴰ (seq' C (C .id) f) .π) .fst .fst)))
            (∧.⟨_,_⟩ c'ᴰ f
              (Cᴰ .Categoryᴰ.idᴰ Cᴰ.⋆ᴰ ∧.π₁ c'ᴰ f)
              (Cᴰ .Categoryᴰ.idᴰ Cᴰ.⋆ᴰ ∧.π₂ c'ᴰ f))
        subgoal f fᴰ = {!!}
        foo : ∀ f (fᴰ : Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ]) →
          ∧.vert c'ᴰ (C .id ⋆⟨ C ⟩ f) ≡ ∧.vert c'ᴰ f
        foo f fᴰ = congS (∧.vert _) (C .⋆IdL _)
        eta : ∀ f fᴰ → PathP (λ i → Cᴰ.Hom[ C .id ⋆⟨ C ⟩ f ][ foo f fᴰ i , cᴰ' ])
          (∧.⟨_,_⟩ c'ᴰ f
            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
             (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))
            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
             (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
              isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ')
              (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst))
          Cᴰ.⋆ᴰ fᴰ)
          (Cᴰ.idᴰ Cᴰ.⋆ᴰ fᴰ)
        eta f fᴰ = congP (λ _ a → a Cᴰ.⋆ᴰ fᴰ) (left f fᴰ ◁ subgoal f fᴰ ▷ ∧.η c'ᴰ f (Cᴰ.idᴰ))
        goal : ∀ f fᴰ → PathP (λ z → ⟨ Pᴰ .F-obᴰ c'ᴰ ((C [-, c ]) .Functor.F-id z f) ⟩)
          ((∧.⟨_,_⟩ c'ᴰ f
            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
              (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))
            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
              (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
                (isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ') (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst))))
          Cᴰ.⋆ᴰ fᴰ)
          fᴰ
        goal f fᴰ = compPathP' (eta f fᴰ) (Cᴰ.⋆IdLᴰ fᴰ)
      Pᴰ .F-seqᴰ = {!!}
