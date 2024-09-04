{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport

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
open CartesianOver
open UniversalElementᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  open Cubical.Categories.Displayed.Reasoning Cᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
  -- TODO: this is already in the library, I just don't want to find it right now
  module _ (c : C .ob) where
    idue : UniversalElement C (C [-, c ])
    idue .vertex = c
    idue .element = C .id
    idue .universal c' .equiv-proof f = uniqueExists
      f (C .⋆IdR _) (λ _ → C .isSetHom _ _) (λ _ p → sym p ∙ C .⋆IdR _)
  -- the universal property of `c'ᴰ ∧ f* cᴰ`,
  -- the vertical binary product of c'ᴰ and the pullback of cᴰ' along f
  module heterogeneous-pair {c' c}
    (f : C [ c' , c ])(c'ᴰ : Cᴰ.ob[ c' ])(cᴰ : Cᴰ.ob[ c ]) where
    spec : Presheafᴰ Cᴰ (C [-, c' ]) _
    spec .F-obᴰ {x = c''} c''ᴰ g =
      Cᴰ.Hom[ g ][ c''ᴰ , c'ᴰ ] × Cᴰ.Hom[ g ⋆⟨ C ⟩ f ][ c''ᴰ , cᴰ ] ,
      isSet× Cᴰ.isSetHomᴰ Cᴰ.isSetHomᴰ
    spec .F-homᴰ {x = c''} {y = c'''} {f = h}
      {xᴰ = c''ᴰ} {yᴰ = c'''ᴰ} hᴰ g (l , r) =
      hᴰ Cᴰ.⋆ᴰ l , reind (sym (C .⋆Assoc _ _ _)) (hᴰ Cᴰ.⋆ᴰ r)
    spec .F-idᴰ {x = c''} {xᴰ = c''ᴰ} = funExt (λ g → funExt (λ (l , r) →
      ΣPathP
        (Cᴰ.⋆IdLᴰ l ,
        ≡[]-rectify (reind-filler-sym _ _ [ _ ]∙[ _ ] Cᴰ.⋆IdLᴰ _))))
    spec .F-seqᴰ {x = c''''} {y = c'''} {z = c''} {f = h} {g = i}
      {xᴰ = c''''ᴰ} {yᴰ = c'''ᴰ} {zᴰ = c''ᴰ} hᴰ iᴰ =
      funExt (λ g → funExt (λ (l , r) → ΣPathP
        (Cᴰ.⋆Assocᴰ _ _ _ ,
        ≡[]-rectify (reind-filler-sym _ _ [ _ ]∙[ _ ]
          Cᴰ.⋆Assocᴰ _ _ _ [ _ ]∙[ _ ]
          ≡[]⋆ refl (sym (C .⋆Assoc _ _ _)) refl (reind-filler _ _) [ _ ]∙[ _ ]
          reind-filler _ _))))
    ue : Type _
    ue = UniversalElementᴰ Cᴰ spec (idue c')
  module _
    (isFib : AllCartesianOvers Cᴰ) {- for typechecking performance -}
    (vps : VerticalBinProducts Cᴰ)
    where
    module  _ {c' c}
      (f : C [ c' , c ])(c'ᴰ : Cᴰ.ob[ c' ])(cᴰ : Cᴰ.ob[ c ])
      where
      private
        module het-pair = heterogeneous-pair f c'ᴰ cᴰ
        module ∧ = VerticalBinProductsAtNotation (vps (c'ᴰ , isFib cᴰ f .f*cᴰ'))
      impl : het-pair.ue
      impl .vertexᴰ = ∧.vert
      impl .elementᴰ = ∧.π₁ , (∧.π₂ Cᴰ.⋆ᴰ isFib cᴰ f .π)
      impl .universalᴰ {f = g} .equiv-proof (l , r) = uniqueExists
        ∧.⟨ l , r* ⟩
        (ΣPathP (
          congS fst (∧.β l r*) ,
          ≡[]-rectify (reind-filler-sym _ _ [ _  ]∙[ _ ]
            symP (Cᴰ.⋆Assocᴰ _ _ _) [ _ ]∙[ _ ]
            ≡[]⋆ refl refl (congS snd (∧.β l r*)) refl [ _ ]∙[ _ ]
            r*-comm)))
        (λ _ → isSet× Cᴰ.isSetHomᴰ Cᴰ.isSetHomᴰ _ _)
        λ gᴰ' p → ≡[]-rectify
          (cong₂ (λ x y → ∧.⟨ x , y ⟩)
            (sym (congS fst p))
            (congS (λ x → isFib cᴰ f .isCartesian _ _ x .fst .fst)
              (sym (congS snd p)) ∙
              congS fst (isFib cᴰ f .isCartesian _ _ _ .snd (_ , ≡[]-rectify (Cᴰ.⋆Assocᴰ _ _ _ [ _ ]∙[ _ ] reind-filler _ _)))))
          ∙ ∧.η gᴰ'
        where
        r* : Cᴰ.Hom[ g  ⋆⟨ C ⟩ C .id ][ _ , isFib cᴰ f .f*cᴰ' ]
        r* = isFib cᴰ f .isCartesian _ _ r .fst .fst
        r*-comm : r* Cᴰ.⋆ᴰ isFib cᴰ f .π ≡ r
        r*-comm = isFib cᴰ f .isCartesian _ _ r .fst .snd
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  open Cubical.Categories.Displayed.Reasoning Cᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
  module _ {c : C .ob}
    (cᴰ cᴰ' : Cᴰ.ob[ c ]) where
    VerticalExponentialsAtSpec : Presheafᴰ Cᴰ (C [-, c ]) _
    VerticalExponentialsAtSpec .F-obᴰ xᴰ f = {!!} , {!!}
    VerticalExponentialsAtSpec .F-homᴰ = {!!}
    VerticalExponentialsAtSpec .F-idᴰ = {!!}
    VerticalExponentialsAtSpec .F-seqᴰ = {!!}
    VerticalExponentialsAt : Type _
    VerticalExponentialsAt = UniversalElementᴰ Cᴰ VerticalExponentialsAtSpec {!!} --(idue c)
--module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
--  (isFib : AllCartesianOvers Cᴰ) {- for typechecking performance -}
--  (vps : VerticalBinProducts Cᴰ)
--  where
--  open CartesianOver
--  open Cubical.Categories.Displayed.Reasoning Cᴰ
--  private
--    module Cᴰ = Categoryᴰ Cᴰ
--  module _ {c : C .ob}
--    (cᴰ cᴰ' : Cᴰ.ob[ c ]) where
--    VerticalExponentialsAt : (cᴰ'' : Cᴰ.ob[ c ]) → Type _
--    VerticalExponentialsAt cᴰ'' = UniversalElementᴰ Cᴰ Pᴰ idue
--      where
--      -- TODO: this is already in the library, I just don't want to find it right now
--      idue : UniversalElement C (C [-, c ])
--      idue .vertex = c
--      idue .element = C .id
--      idue .universal c' .equiv-proof f = uniqueExists
--        f (C .⋆IdR _) (λ _ → C .isSetHom _ _) (λ _ p → sym p ∙ C .⋆IdR _)
--      module _ {c' : C .ob } (c'ᴰ : Cᴰ.ob[ c' ]) where
--        module _ (f : C [ c' , c ]) where
--          module ∧ = VerticalBinProductsAtNotation (vps (c'ᴰ , isFib cᴰ f .f*cᴰ'))
--        module _ (f : C [ c' , c ]) where
--          1⋆f = C .id ⋆⟨ C ⟩ f
--          a : ∧.vert 1⋆f ≡ ∧.vert f
--          a = congS ∧.vert (C .⋆IdL _)
--          b : Cᴰ.Hom[ C .id ][ ∧.vert 1⋆f , c'ᴰ ]
--          b = ∧.π₁ 1⋆f
--          d : Cᴰ.Hom[ C .id ][ ∧.vert 1⋆f , isFib cᴰ 1⋆f .f*cᴰ' ]
--          d = ∧.π₂ 1⋆f
--          e : Cᴰ.Hom[ C .id ][ isFib cᴰ 1⋆f .f*cᴰ' , isFib cᴰ f .f*cᴰ' ]
--          e = isFib cᴰ f .isCartesian (isFib cᴰ 1⋆f .f*cᴰ') (C .id) (isFib cᴰ 1⋆f .π) .fst .fst
--          e' : ∃![ gᴰ ∈ Cᴰ.Hom[ C .id ][ isFib cᴰ 1⋆f .f*cᴰ' , isFib cᴰ f .f*cᴰ' ] ]
--            (gᴰ Cᴰ.⋆ᴰ isFib cᴰ f .π ≡ isFib cᴰ 1⋆f .π)
--          e' = isFib cᴰ f .isCartesian (isFib cᴰ 1⋆f .f*cᴰ') (C .id) (isFib cᴰ 1⋆f .π)
--          h : Cᴰ.Hom[ C .id ][ ∧.vert 1⋆f , ∧.vert f ]
--          h = ∧.⟨_,_⟩ f (b Cᴰ.⋆ᴰ Cᴰ.idᴰ) (d Cᴰ.⋆ᴰ e)
--          n : PathP (λ i → Cᴰ.Hom[ C .id ][ isFib cᴰ (C .⋆IdL f i) .f*cᴰ' , isFib cᴰ f .f*cᴰ' ])
--            e
--            (Cᴰ.idᴰ {p = isFib cᴰ f .f*cᴰ'})
--          n = {!!}
--          m : PathP (λ i → {!!}) (d Cᴰ.⋆ᴰ e) (d Cᴰ.⋆ᴰ Cᴰ.idᴰ)
--          m = {!!}
--          l : h ≡ ∧.⟨_,_⟩ f (Cᴰ.idᴰ Cᴰ.⋆ᴰ b) (d Cᴰ.⋆ᴰ e)
--          l = congS (λ x → ∧.⟨ f , x ⟩ (d Cᴰ.⋆ᴰ e)) (≡[]-rectify (Cᴰ.⋆IdRᴰ _ [ _ ]∙[ _ ] symP (Cᴰ.⋆IdLᴰ _)))
--          k : PathP (λ i → Cᴰ.Hom[ C .id ][ ∧.vert (C .⋆IdL f i) , ∧.vert f ])
--            h
--            (Cᴰ.idᴰ {p = ∧.vert f})
--          k = {!!}
--          module _ (fᴰ : Cᴰ.Hom[ f ][ ∧.vert f , cᴰ' ]) where
--            bruh : PathP (λ i → Cᴰ.Hom[ C .id ][ congS {y = f} ∧.vert (C .⋆IdL _) i , ∧.vert f ])
--              (∧.⟨_,_⟩' f
--                (∧.π₁ (C .id ⋆⟨ C ⟩ f))
--                (transport (congS (λ x → Cᴰ.Hom[ C .id ][ ∧.vert (C .id ⋆⟨ C ⟩ f) , isFib cᴰ x .f*cᴰ' ]) (C .⋆IdL f)) (∧.π₂ (C .id ⋆⟨ C ⟩ f))))
--              (Cᴰ.idᴰ {p = ∧.vert f})
--            bruh i = {!∧.η (C .⋆IdL f i) (Cᴰ.idᴰ) i!}
--      module _ where
--        Pᴰ' : Presheafᴰ Cᴰ (C [-, c ]) _
--        Pᴰ' .F-obᴰ {x = c'} c'ᴰ f = Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ] , Cᴰ.isSetHomᴰ
--        Pᴰ' .F-homᴰ {x = c'} {y = c''} {f = g} {xᴰ = c'ᴰ} {yᴰ = c''ᴰ} gᴰ f fᴰ =
--          ∧.⟨_,_⟩' c'ᴰ f
--            (reind (C .⋆IdL _) (∧.π₁ c''ᴰ (g ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ gᴰ))
--            (reind (C .⋆IdL _) (∧.π₂ c''ᴰ (g ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ isFib cᴰ f .isCartesian _ g (isFib cᴰ (g ⋆⟨ C ⟩ f) .π) .fst .fst))
--          Cᴰ.⋆ᴰ fᴰ
--        Pᴰ' .F-idᴰ {x = c'} {xᴰ = c'ᴰ} = funExt (λ f → funExt (λ fᴰ → goal f fᴰ))
--          where
--          goal : ∀ f fᴰ → PathP
--            (λ i → Cᴰ.Hom[ C .⋆IdL f i ][ ∧.vert c'ᴰ (C .⋆IdL f i) , cᴰ' ])
--            ((VerticalBinProductsAtNotation.⟨ vps (c'ᴰ , isFib cᴰ f .f*cᴰ') ,
--              reind (C .⋆IdL ((C ^op) .id))
--              (Cᴰ .Categoryᴰ._⋆ᴰ_
--               (VerticalBinProductsAtNotation.π₁
--                (vps (c'ᴰ , isFib cᴰ (seq' C ((C ^op) .id) f) .f*cᴰ')))
--               ((Cᴰ ^opᴰ) .Categoryᴰ.idᴰ))
--              ⟩'
--              (reind (C .⋆IdL ((C ^op) .id))
--               (Cᴰ .Categoryᴰ._⋆ᴰ_
--                (VerticalBinProductsAtNotation.π₂
--                 (vps (c'ᴰ , isFib cᴰ (seq' C ((C ^op) .id) f) .f*cᴰ')))
--                (isFib cᴰ f .isCartesian (isFib cᴰ (seq' C ((C ^op) .id) f) .f*cᴰ')
--                 ((C ^op) .id) (isFib cᴰ (seq' C ((C ^op) .id) f) .π) .fst .fst)))) Cᴰ.⋆ᴰ
--             fᴰ)
--            fᴰ
--          goal f fᴰ i = {!!}
--        Pᴰ' .F-seqᴰ = {!!}
--      Pᴰ : Presheafᴰ Cᴰ (C [-, c ]) _
--      Pᴰ .F-obᴰ {x = c'} c'ᴰ f = Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ] , Cᴰ.isSetHomᴰ
--      Pᴰ .F-homᴰ {x = c'} {y = c''} {f = g} {xᴰ = c'ᴰ} {yᴰ = c''ᴰ} gᴰ f fᴰ =
--        ∧.⟨_,_⟩ c'ᴰ f
--          (reind (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (∧.π₁ c''ᴰ (g ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ gᴰ))
--          (reind (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (∧.π₂ c''ᴰ (g ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ isFib cᴰ f .isCartesian _ g (isFib cᴰ (g ⋆⟨ C ⟩ f) .π) .fst .fst))
--        Cᴰ.⋆ᴰ fᴰ
--      Pᴰ .F-idᴰ {x = c'} {xᴰ = c'ᴰ} = funExt (λ f → funExt (λ fᴰ → goal f fᴰ))
--        where
--        left : ∀ f (fᴰ : Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ]) →
--          (∧.⟨_,_⟩ c'ᴰ f
--            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
--              (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))
--            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
--              (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
--                isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ')
--                (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst)))
--          ≡ ∧.⟨ c'ᴰ , f ⟩
--            (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ)
--            (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
--              isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ')
--              (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst)
--        left f fᴰ = cong₂ (λ x y → ∧.⟨_,_⟩ c'ᴰ f x y)
--          (≡[]-rectify (symP (reind-filler (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))))
--          (≡[]-rectify (symP (reind-filler (C .⋆IdL _ ∙ sym (C .⋆IdR _)) (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ')
--              (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst))))
--        subgoal : ∀ f (fᴰ : Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ]) →
--          PathP (λ i → Cᴰ.Hom[ C .id ][ ∧.vert c'ᴰ (C .⋆IdL f i) , ∧.vert c'ᴰ f ])
--            (∧.⟨_,_⟩ c'ᴰ f
--              (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ)
--              (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
--                isFib cᴰ f .isCartesian (isFib cᴰ (seq' C (C .id) f) .f*cᴰ')
--                (C .id) (isFib cᴰ (seq' C (C .id) f) .π) .fst .fst))
--            (∧.⟨_,_⟩ c'ᴰ f
--              (Cᴰ .Categoryᴰ.idᴰ Cᴰ.⋆ᴰ ∧.π₁ c'ᴰ f)
--              (Cᴰ .Categoryᴰ.idᴰ Cᴰ.⋆ᴰ ∧.π₂ c'ᴰ f))
--        subgoal f fᴰ = congP₂ (λ i x y → ∧.⟨_,_⟩ c'ᴰ f x y)
--          (transport {!!} (compPathP (Cᴰ.⋆IdRᴰ (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f))) (compPathP (congP (λ _ x → ∧.π₁ c'ᴰ x) (C .⋆IdL f)) (symP (Cᴰ.⋆IdLᴰ (∧.π₁ c'ᴰ f)))))) --(compPathP' (Cᴰ.⋆IdRᴰ _) (compPathP' (congP (λ _ x → ∧.π₁ c'ᴰ x) (C .⋆IdL _)) (symP (Cᴰ.⋆IdLᴰ _))))
--          {!!}
--        foo : ∀ f (fᴰ : Cᴰ.Hom[ f ][ ∧.vert c'ᴰ f , cᴰ' ]) →
--          ∧.vert c'ᴰ (C .id ⋆⟨ C ⟩ f) ≡ ∧.vert c'ᴰ f
--        foo f fᴰ = congS (∧.vert _) (C .⋆IdL _)
--        eta : ∀ f fᴰ → PathP (λ i → Cᴰ.Hom[ C .id ⋆⟨ C ⟩ f ][ foo f fᴰ i , cᴰ' ])
--          (∧.⟨_,_⟩ c'ᴰ f
--            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
--             (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))
--            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
--             (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
--              isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ')
--              (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst))
--          Cᴰ.⋆ᴰ fᴰ)
--          (Cᴰ.idᴰ Cᴰ.⋆ᴰ fᴰ)
--        eta f fᴰ = congP (λ _ a → a Cᴰ.⋆ᴰ fᴰ) (left f fᴰ ◁ subgoal f fᴰ ▷ ∧.η c'ᴰ f (Cᴰ.idᴰ))
--        goal : ∀ f fᴰ → PathP (λ z → Cᴰ.Hom[ C .⋆IdL f z ][ ∧.vert c'ᴰ (C .⋆IdL f z) , cᴰ' ])
--          ((∧.⟨_,_⟩ c'ᴰ f
--            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
--              (∧.π₁ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ Cᴰ.idᴰ))
--            (reind (C .⋆IdL (C .id) ∙ sym (C .⋆IdR (C .id)))
--              (∧.π₂ c'ᴰ (C .id ⋆⟨ C ⟩ f) Cᴰ.⋆ᴰ
--                (isFib cᴰ f .isCartesian (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .f*cᴰ') (C .id) (isFib cᴰ (C .id ⋆⟨ C ⟩ f) .π) .fst .fst))))
--          Cᴰ.⋆ᴰ fᴰ)
--          fᴰ
--        goal f fᴰ = {!compPathP' (eta f fᴰ) (Cᴰ.⋆IdLᴰ fᴰ)!}
--      Pᴰ .F-seqᴰ = {!!}
