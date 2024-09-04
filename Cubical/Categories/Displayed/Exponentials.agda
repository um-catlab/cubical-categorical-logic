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
    module HetPairNotation (hp : ue) where
      vert : Cᴰ.ob[ c' ]
      vert = hp .vertexᴰ
      π₁₂ : Cᴰ.Hom[ C .id ][ vert , c'ᴰ ] × Cᴰ.Hom[ C .id ⋆⟨ C ⟩ f ][ vert , cᴰ ]
      π₁₂ = hp .elementᴰ
      π₁ = π₁₂ .fst
      π₂ = π₁₂ .snd
      module _ {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{g : C [ x , c' ]} where
        ⟨_,_⟩ : Cᴰ.Hom[ g ⋆⟨ C ⟩ C .id ][ xᴰ , c'ᴰ ] →
          Cᴰ.Hom[ g ⋆⟨ C ⟩ C .id ⋆⟨ C ⟩ f ][ xᴰ , cᴰ ] →
          Cᴰ.Hom[ g ][ xᴰ , vert ]
        ⟨ gᴰ , g⋆fᴰ ⟩ = invIsEq (hp .universalᴰ) (gᴰ , g⋆fᴰ)
  AllHetPairs : Type _
  AllHetPairs = ∀{c' c}
    (f : C [ c' , c ])(c'ᴰ : Cᴰ.ob[ c' ])(cᴰ : Cᴰ.ob[ c ]) →
    heterogeneous-pair.ue f c'ᴰ cᴰ
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
  (ahp : AllHetPairs Cᴰ)
  where
  open Cubical.Categories.Displayed.Reasoning Cᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
  module _ {c : C .ob}
    (cᴰ cᴰ' : Cᴰ.ob[ c ]) where
    VerticalExponentialsAtSpec : Presheafᴰ Cᴰ (C [-, c ]) _
    VerticalExponentialsAtSpec .F-obᴰ xᴰ f = Cᴰ.Hom[ f ][ ahp f xᴰ cᴰ .vertexᴰ , cᴰ' ] , Cᴰ.isSetHomᴰ
    VerticalExponentialsAtSpec .F-homᴰ {f = g} {xᴰ = xᴰ} gᴰ f fᴰ = {!heterogeneous-pair.HetPairNotation.⟨_,_⟩ Cᴰ ? ? ? (ahp f xᴰ cᴰ)!} Cᴰ.⋆ᴰ fᴰ
    VerticalExponentialsAtSpec .F-idᴰ = {!!}
    VerticalExponentialsAtSpec .F-seqᴰ = {!!}
    VerticalExponentialsAt : Type _
    VerticalExponentialsAt = UniversalElementᴰ Cᴰ VerticalExponentialsAtSpec {!!} --(idue c)
