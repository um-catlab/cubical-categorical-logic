module Cubical.Categories.LocallySmall.Constructions.BinProduct.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Prod using (_×ω_; _,_)

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base
open import Cubical.Categories.LocallySmall.Instances.Functor
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Constructions.BinProduct.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base

open Category
open Σω
open Functor

module _
  {C : Category Cob CHom-ℓ}
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  where
  _,F_ : Functor C D → Functor C E → Functor C (D ×C E)
  (F ,F G) .F-ob = λ z → F-ob F z , F-ob G z
  (F ,F G) .F-hom = λ z → F-hom F z , F-hom G z
  (F ,F G) .F-id = ≡-× (F-id F) (F-id G)
  (F ,F G) .F-seq _ _ = ≡-× (F-seq F _ _) (F-seq G _ _)

module _
  {D : Category Dob DHom-ℓ}
  {E : Category Eob EHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  {Eobᴰ-ℓ Eobᴰ EHom-ℓᴰ}
  (C : SmallCategory ℓC ℓC')
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  (Eᴰ : SmallFibersCategoryᴰ E Eobᴰ-ℓ Eobᴰ EHom-ℓᴰ)
  where
  private
    module C =  SmallCategory C
    module D =  CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module E =  CategoryNotation E
    module Eᴰ = CategoryᴰNotation Eᴰ
    module D×E =  CategoryNotation (D ×C E)
    module Dᴰ×ᴰEᴰ =  CategoryᴰNotation (Dᴰ ×CᴰSF Eᴰ)
  open SmallFibNatTrans

  open Functorᴰ

  ,F-SFFunctorⱽ :
    Functorⱽ
      (FIBER-FUNCTOR C Dᴰ ×Cᴰ FIBER-FUNCTOR C Eᴰ)
      (FIBER-FUNCTOR C (Dᴰ ×CᴰSF Eᴰ))
  ,F-SFFunctorⱽ .F-obᴰ (F , G) =
    ProductOfFibers→×CᴰSFFiber Dᴰ Eᴰ ∘F (F ,F G)
  ,F-SFFunctorⱽ .F-homᴰ fᴰ .N-ob x = fᴰ .fst .N-ob x , fᴰ .snd .N-ob x
  ,F-SFFunctorⱽ .F-homᴰ {xᴰ = xᴰ}{yᴰ = yᴰ} (α , β) .N-hom g =
     -- Should this be done more directly instead of using
     -- N-hom'→N-hom?
     N-hom'→N-hom (Dᴰ ×CᴰSF Eᴰ) _
       (ProductOfFibers→×CᴰSFFiber Dᴰ Eᴰ ∘F (xᴰ .fst ,F xᴰ .snd))
       (ProductOfFibers→×CᴰSFFiber Dᴰ Eᴰ ∘F (yᴰ .fst ,F yᴰ .snd))
       (,F-SFFunctorⱽ .F-homᴰ (α , β) .N-ob) g
       (ΣPathP (D×E.⋆IdL _ ∙ (sym $ D×E.⋆IdR _) ,
               ΣPathP (
                 (Dᴰ.rectify (Dᴰ.≡out $ N-hom' α g)) ,
                 (Eᴰ.rectify (Eᴰ.≡out $ N-hom' β g)))))
  ,F-SFFunctorⱽ .F-idᴰ = makeSFNatTransPath refl (λ _ → refl)
  ,F-SFFunctorⱽ .F-seqᴰ _ _ = makeSFNatTransPath refl (λ _ → refl)
