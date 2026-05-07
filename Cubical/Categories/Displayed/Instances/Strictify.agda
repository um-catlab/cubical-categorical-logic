{-
  Yoneda strictification of a displayed category.
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Strictify where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Instances.Strictify
open import Cubical.Categories.Instances.Fiber

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.StrictHom

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Categoryᴰ
open Functorᴰ
open NatTransᴰ
open NatIsoᴰ
open isIsoᴰ
open PshHomStrict
open PshHomStrictᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰf = Fibers Cᴰ
    module Cᴰ = Categoryᴰ Cᴰ

  YonedaStrictifyᴰ
    : Categoryᴰ (YonedaStrictify C)
        ℓCᴰ
        (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
  YonedaStrictifyᴰ .ob[_] = Cᴰ.ob[_]
  YonedaStrictifyᴰ .Hom[_][_,_] α xᴰ yᴰ =
    PshHomStrictᴰ α (Cᴰ [-][-, xᴰ ]) (Cᴰ [-][-, yᴰ ])
  YonedaStrictifyᴰ .idᴰ = idPshHomStrictᴰ
  YonedaStrictifyᴰ ._⋆ᴰ_ = _⋆PshHomStrictᴰ_
  YonedaStrictifyᴰ .⋆IdLᴰ _ = refl
  YonedaStrictifyᴰ .⋆IdRᴰ _ = refl
  YonedaStrictifyᴰ .⋆Assocᴰ _ _ _ = refl
  YonedaStrictifyᴰ .isSetHomᴰ = isSetPshHomStrictᴰ _ _ _

  toYonedaStrictifyᴰ : Functorᴰ (toYonedaStrictify C) Cᴰ YonedaStrictifyᴰ
  toYonedaStrictifyᴰ .F-obᴰ xᴰ = xᴰ
  toYonedaStrictifyᴰ .F-homᴰ fᴰ .N-obᴰ Γ Γᴰ p pᴰ = pᴰ Cᴰ.⋆ᴰ fᴰ
  toYonedaStrictifyᴰ .F-homᴰ {f = f} fᴰ .N-homᴰ Δ Γ Δᴰ Γᴰ g p' p gᴰ pᴰ' pᴰ e eᴰ =
    Cᴰf.rectifyOut $ sym (Cᴰf.≡in (Cᴰ.⋆Assocᴰ gᴰ pᴰ' fᴰ)) ∙ Cᴰf.⟨ Cᴰf.≡in eᴰ ⟩⋆⟨ refl ⟩
  toYonedaStrictifyᴰ .F-idᴰ =
    makePshHomStrictᴰPathP (λ i Γ Γᴰ p pᴰ → Cᴰ.⋆IdRᴰ pᴰ i)
  toYonedaStrictifyᴰ .F-seqᴰ fᴰ gᴰ =
    makePshHomStrictᴰPathP (λ i Γ Γᴰ p pᴰ → symP (Cᴰ.⋆Assocᴰ pᴰ fᴰ gᴰ) i)

  fromYonedaStrictifyᴰ : Functorᴰ (fromYonedaStrictify C) YonedaStrictifyᴰ Cᴰ
  fromYonedaStrictifyᴰ .F-obᴰ = λ z → z
  fromYonedaStrictifyᴰ .F-homᴰ = λ z →
                                    z .N-obᴰ (fromYonedaStrictify C .Functor.F-ob _)
                                    (F-obᴰ fromYonedaStrictifyᴰ _) C.id Cᴰ.idᴰ
  fromYonedaStrictifyᴰ .F-idᴰ = refl
  fromYonedaStrictifyᴰ .F-seqᴰ f g = Cᴰf.rectifyOut $ sym $ Cᴰf.≡in $
    g .PshHomStrictᴰ.N-homᴰ _ _ _ _ _ _ _ _ _ _ (C.⋆IdR _) (Cᴰ.⋆IdRᴰ _)

  from-to-YonedaStrictifyᴰ
    : NatIsoᴰ (from-to-YonedaStrictify C)
        (fromYonedaStrictifyᴰ ∘Fᴰ toYonedaStrictifyᴰ) Idᴰ
  from-to-YonedaStrictifyᴰ .transᴰ .N-obᴰ _ = Cᴰ.idᴰ
  from-to-YonedaStrictifyᴰ .transᴰ .N-homᴰ fᴰ = Cᴰ.⋆IdRᴰ _
  from-to-YonedaStrictifyᴰ .nIsoᴰ xᴰ .invᴰ = Cᴰ.idᴰ
  from-to-YonedaStrictifyᴰ .nIsoᴰ xᴰ .secᴰ = Cᴰ.⋆IdLᴰ _
  from-to-YonedaStrictifyᴰ .nIsoᴰ xᴰ .retᴰ = Cᴰ.⋆IdLᴰ _

  to-from-YonedaStrictifyᴰ
    : NatIsoᴰ (to-from-YonedaStrictify C)
        (toYonedaStrictifyᴰ ∘Fᴰ fromYonedaStrictifyᴰ) Idᴰ
  to-from-YonedaStrictifyᴰ .transᴰ .N-obᴰ _ = idPshHomStrictᴰ
  to-from-YonedaStrictifyᴰ .transᴰ .N-homᴰ {x = x}{xᴰ = xᴰ} fᴰ =
    makePshHomStrictᴰPathP (λ i Γ Γᴰ p pᴰ →
      fᴰ .N-homᴰ Γ x Γᴰ xᴰ p C.id p pᴰ Cᴰ.idᴰ pᴰ (C.⋆IdR p) (Cᴰ.⋆IdRᴰ pᴰ) i)
  to-from-YonedaStrictifyᴰ .nIsoᴰ xᴰ .invᴰ = idPshHomStrictᴰ
  to-from-YonedaStrictifyᴰ .nIsoᴰ xᴰ .secᴰ = refl
  to-from-YonedaStrictifyᴰ .nIsoᴰ xᴰ .retᴰ = refl
