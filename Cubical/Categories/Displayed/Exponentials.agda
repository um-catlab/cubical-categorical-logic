{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

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
      module _ {c' : C .ob } (c'ᴰ : Cᴰ.ob[ c' ]) where
        module _ (f : C [ c' , c ]) where
          module ∧ = VerticalBinProductsAtNotation (vps (c'ᴰ , isFib cᴰ f .f*cᴰ'))
        -- TODO: draw this out. I think there's too many reinds
        module _ (f : C [ c' , c ]) where
          1⋆f = C .id ⋆⟨ C ⟩ f
          hmmm : ∧.vert 1⋆f ≡ ∧.vert f
          hmmm = cong ∧.vert (C .⋆IdL _)
          isuckatthis : CatIsoᴰ Cᴰ idCatIso (∧.vert 1⋆f) (∧.vert f)
          isuckatthis = subst (CatIsoᴰ Cᴰ idCatIso (∧.vert 1⋆f)) hmmm (idᴰCatIsoᴰ Cᴰ)
          breh : Cᴰ.Hom[ 1⋆f ][ ∧.vert 1⋆f , cᴰ' ] ≡ Cᴰ.Hom[ f ][ ∧.vert f , cᴰ' ]
          breh = congS (λ x → Cᴰ.Hom[ x ][ ∧.vert x , cᴰ' ]) (C .⋆IdL _)
        bruh : (f : C [ c' , c ]) →
          PathP (λ i → Cᴰ.Hom[ C .id ][ congS {y = f} ∧.vert (C .⋆IdL _) i , ∧.vert f ])
          (∧.⟨_,_⟩' f
            (∧.π₁ (C .id ⋆⟨ C ⟩ f))
            (transport (congS (λ x → Cᴰ.Hom[ C .id ][ ∧.vert (C .id ⋆⟨ C ⟩ f) , isFib cᴰ x .f*cᴰ' ]) (C .⋆IdL f)) (∧.π₂ (C .id ⋆⟨ C ⟩ f))))
          (Cᴰ.idᴰ {p = ∧.vert f})
        bruh f i = {!∧.η (C .⋆IdL f i) (Cᴰ.idᴰ) i!}
        fooo : (f : C [ c' , c ]) → ∧.vert (C .id ⋆⟨ C ⟩ f) ≡ ∧.vert f
        fooo f = congS ∧.vert (C .⋆IdL _)
        gal : (f : C [ c' , c ])(fᴰ : Cᴰ.Hom[ f ][ ∧.vert f , cᴰ' ]) →
          PathP (λ i → Cᴰ.Hom[ C .⋆IdL f i ][ ∧.vert (C .⋆IdL f i) , cᴰ' ])
          (∧.⟨_,_⟩' f
            (∧.π₁ (seq' C (C .id) f))
            (isFib cᴰ f .isCartesian (∧.vert _) (C .id) (∧.π₂ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ reind (C .⋆IdL _) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π)) .fst .fst)
          Cᴰ.⋆ᴰ fᴰ)
          fᴰ
        gal f fᴰ = {!!}
      module _ where
        Pᴰ' : Presheafᴰ Cᴰ (C [-, c ]) _
        Pᴰ' .F-obᴰ {x = c'} c'ᴰ f = Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ] , Cᴰ.isSetHomᴰ
        Pᴰ' .F-homᴰ {x = c'} {y = c''} {f = g} {xᴰ = c'ᴰ} {yᴰ = c''ᴰ} gᴰ f fᴰ =
          ∧.⟨_,_⟩' c'ᴰ f
            (reind (C .⋆IdL _) (∧.π₁ c''ᴰ (g ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ gᴰ))
            (reind (C .⋆IdL _) (∧.π₂ c''ᴰ (g ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ isFib cᴰ f .isCartesian _ g (isFib cᴰ (g ⋆⟨ C ⟩ f) .π) .fst .fst))
          Cᴰ.⋆ᴰ fᴰ
--Goal: PathP
--      (λ i →
--         ⟨
--         Cᴰ .Categoryᴰ.Hom[_][_,_] ((C [-, c ]) .Functor.F-id i f)
--         (VerticalBinProductsAtNotation.vert
--          (vps (c'ᴰ , isFib cᴰ ((C [-, c ]) .Functor.F-id z f) .f*cᴰ')))
--         cᴰ'
--         , Cᴰ .Categoryᴰ.isSetHomᴰ
--         ⟩)
--      (Cᴰ .Categoryᴰ._⋆ᴰ_
--       (VerticalBinProductsAtNotation.⟨ vps (c'ᴰ , isFib cᴰ f .f*cᴰ') ,
--        reind (C .⋆IdL (id C))
--        (Cᴰ .Categoryᴰ._⋆ᴰ_
--         (VerticalBinProductsAtNotation.π₁
--          (vps (c'ᴰ , isFib cᴰ (seq' C (id C) f) .f*cᴰ')))
--         ((Cᴰ ^opᴰ) .Categoryᴰ.idᴰ))
--        ⟩'
--        (reind (C .⋆IdL (id C))
--         (Cᴰ .Categoryᴰ._⋆ᴰ_
--          (VerticalBinProductsAtNotation.π₂
--           (vps (c'ᴰ , isFib cᴰ (seq' C (id C) f) .f*cᴰ')))
--          (isFib cᴰ f .isCartesian (isFib cᴰ (seq' C (id C) f) .f*cᴰ') (id C)
--           (isFib cᴰ (seq' C (id C) f) .π) .fst .fst))))
--       fᴰ)
--      fᴰ
        Pᴰ' .F-idᴰ {x = c'} {xᴰ = c'ᴰ} = funExt (λ f → funExt (λ fᴰ → goal f fᴰ))
          where
          goal : ∀ f fᴰ → PathP
            (λ i → Cᴰ.Hom[ C .⋆IdL f i ][ ∧.vert c'ᴰ (C .⋆IdL f i) , cᴰ' ])
            ((VerticalBinProductsAtNotation.⟨ vps (c'ᴰ , isFib cᴰ f .f*cᴰ') ,
              reind (C .⋆IdL ((C ^op) .id))
              (Cᴰ .Categoryᴰ._⋆ᴰ_
               (VerticalBinProductsAtNotation.π₁
                (vps (c'ᴰ , isFib cᴰ (seq' C ((C ^op) .id) f) .f*cᴰ')))
               ((Cᴰ ^opᴰ) .Categoryᴰ.idᴰ))
              ⟩'
              (reind (C .⋆IdL ((C ^op) .id))
               (Cᴰ .Categoryᴰ._⋆ᴰ_
                (VerticalBinProductsAtNotation.π₂
                 (vps (c'ᴰ , isFib cᴰ (seq' C ((C ^op) .id) f) .f*cᴰ')))
                (isFib cᴰ f .isCartesian (isFib cᴰ (seq' C ((C ^op) .id) f) .f*cᴰ')
                 ((C ^op) .id) (isFib cᴰ (seq' C ((C ^op) .id) f) .π) .fst .fst)))) Cᴰ.⋆ᴰ
             fᴰ)
            fᴰ
          goal f fᴰ i = {!!}
            where
            one : PathP
                   (λ j → Cᴰ.Hom[ C .⋆IdL f j ][ ∧.vert c'ᴰ f , cᴰ' ])
                   (Cᴰ.idᴰ Cᴰ.⋆ᴰ fᴰ)
                   fᴰ
            one = Cᴰ.⋆IdLᴰ fᴰ
            half : PathP {!!}
              (∧.⟨_,_⟩' c'ᴰ f (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f)) {!!})
              Cᴰ.idᴰ
            half = {!!}
            two : PathP (λ j → Cᴰ.Hom[ C .⋆IdL f j ][ ∧.vert c'ᴰ (C .⋆IdL f j) , cᴰ' ])
              {!!}
              fᴰ
            two = {!!}
        Pᴰ' .F-seqᴰ = {!!}
      Pᴰ : Presheafᴰ Cᴰ (C [-, c ]) _
      Pᴰ .F-obᴰ {x = c'} c'ᴰ f = Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ] , Cᴰ.isSetHomᴰ
      Pᴰ .F-homᴰ {x = c'} {y = c''} {f = g} {xᴰ = c'ᴰ} {yᴰ = c''ᴰ} gᴰ f fᴰ =
        ∧.⟨_,_⟩ c'ᴰ f
          (reind (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (∧.π₁ c''ᴰ (g ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ gᴰ))
          (reind (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (∧.π₂ c''ᴰ (g ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ isFib cᴰ f .isCartesian _ g (isFib cᴰ (g ⋆⟨ C ⟩ f) .π) .fst .fst))
        Cᴰ.⋆ᴰ fᴰ
      Pᴰ .F-idᴰ {x = c'} {xᴰ = c'ᴰ} = funExt (λ f → funExt (λ fᴰ → goal f fᴰ))
        where
        left : ∀ f (fᴰ : Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ]) →
          (∧.⟨_,_⟩ c'ᴰ f
            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
              (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))
            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
              (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
                isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ')
                (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst)))
          ≡ ∧.⟨ c'ᴰ , f ⟩
            (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ)
            (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
              isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ')
              (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst)
        left f fᴰ = cong₂ (λ x y → ∧.⟨_,_⟩ c'ᴰ f x y)
          (≡[]-rectify (symP (reind-filler (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))))
          (≡[]-rectify (symP (reind-filler (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ')
              (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst))))
        subgoal : ∀ f (fᴰ : Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ]) →
          PathP (λ i → Cᴰ.Hom[ C .id ][ ∧.vert c'ᴰ (C .⋆IdL f i) , ∧.vert c'ᴰ f ])
            (∧.⟨_,_⟩ c'ᴰ f
              (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ)
              (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
                isFib cᴰ f .isCartesian (isFib cᴰ (seq' C (C .id) f) .f*cᴰ')
                (C .id) (isFib cᴰ (seq' C (C .id) f) .π) .fst .fst))
            (∧.⟨_,_⟩ c'ᴰ f
              (Cᴰ .Categoryᴰ.idᴰ Cᴰ.⋆ᴰ ∧.π₁ c'ᴰ f)
              (Cᴰ .Categoryᴰ.idᴰ Cᴰ.⋆ᴰ ∧.π₂ c'ᴰ f))
        subgoal f fᴰ = congP₂ (λ i x y → ∧.⟨_,_⟩ c'ᴰ f x y)
          (transport {!!} (compPathP (Cᴰ.⋆IdRᴰ (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f))) (compPathP (congP (λ _ x → ∧.π₁ c'ᴰ x) (C .⋆IdL f)) (symP (Cᴰ.⋆IdLᴰ (∧.π₁ c'ᴰ f)))))) --(compPathP' (Cᴰ.⋆IdRᴰ _) (compPathP' (congP (λ _ x → ∧.π₁ c'ᴰ x) (C .⋆IdL _)) (symP (Cᴰ.⋆IdLᴰ _))))
          {!!}
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
        goal : ∀ f fᴰ → PathP (λ z → Cᴰ.Hom[ C .⋆IdL f z ][ ∧.vert c'ᴰ (C .⋆IdL f z) , cᴰ' ])
          ((∧.⟨_,_⟩ c'ᴰ f
            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
              (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))
            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
              (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
                (isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ') (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst))))
          Cᴰ.⋆ᴰ fᴰ)
          fᴰ
        goal f fᴰ = {!compPathP' (eta f fᴰ) (Cᴰ.⋆IdLᴰ fᴰ)!}
      Pᴰ .F-seqᴰ = {!!}
