module Cubical.Categories.LocallySmall.Displayed.Category.Notation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Sigma.More


open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Functor.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base
open import Cubical.Categories.LocallySmall.Variables.Category

open Category
open Categoryᴰ
open Σω

module _ {C : Category Cob CHom-ℓ}(Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ) where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
  module CategoryᴰNotation where
    open Categoryᴰ Cᴰ public
    module ∫C = CategoryNotation Cᴰ.∫C

    open Functor
    Fst : Functor Cᴰ.∫C C
    Fst .F-ob = λ z → z .fst
    Fst .F-hom = λ z → z .fst
    Fst .F-id = refl
    Fst .F-seq = λ _ _ → refl

    open Section
    Snd : Section Fst Cᴰ
    Snd .F-obᴰ = λ d → d .snd
    Snd .F-homᴰ = λ f → f .snd
    Snd .F-idᴰ = refl
    Snd .F-seqᴰ = λ _ _ → refl

    ISOCᴰ = ISOᴰ Cᴰ
    module ISOCᴰ = Categoryᴰ ISOCᴰ
    ISOCᴰ≡ :
      ∀ {x y : Cob}{f g : C.ISOC.Hom[ x , y ]}
      {xᴰ yᴰ}{fᴰ : ISOCᴰ.Hom[ f ][ xᴰ , yᴰ ]}{gᴰ : ISOCᴰ.Hom[ g ][ xᴰ , yᴰ ]}
      → fᴰ .CatIsoᴰ.funᴰ Cᴰ.∫≡ gᴰ .CatIsoᴰ.funᴰ
      → fᴰ ISOCᴰ.∫≡ gᴰ
    ISOCᴰ≡ = CatIsoᴰ≡ Cᴰ

    invCatIsoᴰ : ∀ {x y xᴰ yᴰ}{f : C.ISOC.Hom[ x , y ]}
      → (fᴰ : CatIsoᴰ Cᴰ f xᴰ yᴰ)
      → CatIsoᴰ Cᴰ (C.invCatIso f) yᴰ xᴰ
    invCatIsoᴰ fᴰ .CatIsoᴰ.funᴰ = fᴰ .CatIsoᴰ.invᴰ
    invCatIsoᴰ fᴰ .CatIsoᴰ.invᴰ = fᴰ .CatIsoᴰ.funᴰ
    invCatIsoᴰ fᴰ .CatIsoᴰ.secᴰ = fᴰ .CatIsoᴰ.retᴰ
    invCatIsoᴰ fᴰ .CatIsoᴰ.retᴰ = fᴰ .CatIsoᴰ.secᴰ

    -- Can probably get this from ∫ somehow
    CatIsoᴰ⋆ᴰ-Iso-over : ∀ {x y xᴰ yᴰ}{f : C.ISOC.Hom[ x , y ]}
      → CatIsoᴰ Cᴰ f xᴰ yᴰ
      → ∀ {z}{zᴰ : Cobᴰ z}
      → IsoOver (C.CatIso⋆-Iso f) Cᴰ.Hom[_][ yᴰ , zᴰ ] Cᴰ.Hom[_][ xᴰ , zᴰ ]
    CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.fun g gᴰ = fᴰ .CatIsoᴰ.funᴰ Cᴰ.⋆ᴰ gᴰ
    CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.inv g gᴰ = fᴰ .CatIsoᴰ.invᴰ Cᴰ.⋆ᴰ gᴰ
    CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.rightInv g gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ fᴰ .CatIsoᴰ.retᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdL _
    CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.leftInv g gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ fᴰ .CatIsoᴰ.secᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdL _

    v[_] : (c : Cob) → Category (Cobᴰ c) (CHom-ℓᴰ c c)
    v[_] = fib Cᴰ

    module _ (C-⋆ : C.Id⋆Eq) where
      vEq⟨_⟩[_] : (c : Cob) → Category (Cobᴰ c) (CHom-ℓᴰ c c)
      vEq⟨_⟩[_] = fibEq Cᴰ C-⋆

    module Cⱽ {c : Cob} = Category (v[ c ])

    CatIsoⱽ→CatIsoFiber : ∀ {x}{xᴰ yᴰ : Cobᴰ x}
      (fⱽ : CatIsoⱽ Cᴰ xᴰ yᴰ)
      → CatIso v[ x ] xᴰ yᴰ
    CatIsoⱽ→CatIsoFiber fⱽ .CatIso.fun = fⱽ .CatIsoᴰ.funᴰ
    CatIsoⱽ→CatIsoFiber fⱽ .CatIso.inv = fⱽ .CatIsoᴰ.invᴰ
    CatIsoⱽ→CatIsoFiber fⱽ .CatIso.sec = Cᴰ.rectify $ Cᴰ.≡out $
      sym (Cᴰ.reind-filler _ _)
      ∙ fⱽ .CatIsoᴰ.secᴰ
      ∙ Cᴰ.reind-filler _ _
    CatIsoⱽ→CatIsoFiber fⱽ .CatIso.ret = Cᴰ.rectify $ Cᴰ.≡out $
      sym (Cᴰ.reind-filler _ _)
      ∙ fⱽ .CatIsoᴰ.retᴰ
      ∙ Cᴰ.reind-filler _ _
