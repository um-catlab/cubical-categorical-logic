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
        --subsubgoal : ∀ f fᴰ → PathP
        --                       (λ z →
        --                          Cᴰ .Categoryᴰ.Hom[_][_,_] {!!} {!!}
        --                          (vps (c'ᴰ , isFib cᴰ f .f*cᴰ') .UniversalElementᴰ.vertexᴰ))
        --                       (VerticalBinProductsAtNotation.⟨ vps (c'ᴰ , isFib cᴰ f .f*cᴰ') ,
        --                        reind (C .⋆IdL ((C ^op) .id) ∙ (λ i → C .⋆IdR ((C ^op) .id) (~ i)))
        --                        (Cᴰ .Categoryᴰ._⋆ᴰ_
        --                         (VerticalBinProductsAtNotation.π₁
        --                          (vps (c'ᴰ , isFib cᴰ (seq' C ((C ^op) .id) f) .f*cᴰ')))
        --                         ((Cᴰ ^opᴰ) .Categoryᴰ.idᴰ))
        --                        ⟩
        --                        (reind
        --                         (C .⋆IdL ((C ^op) .id) ∙ (λ i → C .⋆IdR ((C ^op) .id) (~ i)))
        --                         (Cᴰ .Categoryᴰ._⋆ᴰ_
        --                          (VerticalBinProductsAtNotation.π₂
        --                           (vps (c'ᴰ , isFib cᴰ (seq' C ((C ^op) .id) f) .f*cᴰ')))
        --                          (isFib cᴰ f .isCartesian (isFib cᴰ (seq' C ((C ^op) .id) f) .f*cᴰ')
        --                           ((C ^op) .id) (isFib cᴰ (seq' C ((C ^op) .id) f) .π) .fst .fst))))
        --                       (Cᴰ .Categoryᴰ.idᴰ)
        --subsubgoal f fᴰ = {!!}
        --subgoal : ∀ f fᴰ → PathP (λ i → Cᴰ .Categoryᴰ.Hom[_][_,_] (C ._⋆_ {!!} f) {!!} cᴰ')
        --                    (Cᴰ .Categoryᴰ._⋆ᴰ_ _ fᴰ) (Cᴰ .Categoryᴰ._⋆ᴰ_ _ fᴰ)
        subgoal : ∀ f fᴰ → PathP (λ i → Cᴰ .Categoryᴰ.Hom[_][_,_] (C ._⋆_ (C .id) f) {!!} cᴰ')
          (Cᴰ .Categoryᴰ._⋆ᴰ_ (VerticalBinProductsAtNotation.⟨ vps (c'ᴰ , isFib cᴰ f .f*cᴰ') , reind (C .⋆IdL (id C) ∙ (λ i → C .⋆IdR (id C) (~ i))) (Cᴰ .Categoryᴰ._⋆ᴰ_ (VerticalBinProductsAtNotation.π₁ (vps (c'ᴰ , isFib cᴰ (seq' C (id C) f) .f*cᴰ'))) Cᴰ.idᴰ)⟩ (reind (C .⋆IdL (id C) ∙ (λ i → C .⋆IdR (id C) (~ i))) (Cᴰ .Categoryᴰ._⋆ᴰ_ (VerticalBinProductsAtNotation.π₂ (vps (c'ᴰ , isFib cᴰ (seq' C (id C) f) .f*cᴰ'))) (isFib cᴰ f .isCartesian (isFib cᴰ (seq' C (id C) f) .f*cᴰ') (id C) (isFib cᴰ (seq' C (id C) f) .π) .fst .fst)))) fᴰ)
          (Cᴰ .Categoryᴰ._⋆ᴰ_ (Cᴰ .Categoryᴰ.idᴰ) fᴰ)
        subgoal f fᴰ = congP (λ i a → a Cᴰ.⋆ᴰ fᴰ) {!!}
        goal : ∀ f fᴰ → PathP (λ z → ⟨ Pᴰ .F-obᴰ c'ᴰ ((C [-, c ]) .Functor.F-id z f) ⟩)
                         (Pᴰ .F-homᴰ ((Cᴰ ^opᴰ) .Categoryᴰ.idᴰ) f fᴰ)
                         (Categoryᴰ.idᴰ (SETᴰ ℓC' ℓCᴰ') f fᴰ)
        goal f fᴰ = compPathP' (subgoal f fᴰ) (Cᴰ.⋆IdLᴰ fᴰ)
      Pᴰ .F-seqᴰ = {!!}
