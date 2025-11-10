module Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Prod using (_×ω_; _,_)

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered
open import Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibered
open import Cubical.Categories.LocallySmall.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Constructions.BinProduct.Properties

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Category
open Categoryᴰ
open Σω

module _
  {C : Category Cob CHom-ℓ}(Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  {D : Category Dob DHom-ℓ}(Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ

  _×Cᴰ_ : Categoryᴰ (C ×C D)
            (λ (c , d) → Σω[ cᴰ ∈ Cobᴰ c ] Dobᴰ d)
            _
  _×Cᴰ_ .Hom[_][_,_] (f , g) (c , d) (c' , d') =
    Cᴰ.Hom[ f ][ c , c' ] × Dᴰ.Hom[ g ][ d , d' ]
  _×Cᴰ_ .idᴰ = Cᴰ.idᴰ , Dᴰ.idᴰ
  _×Cᴰ_ ._⋆ᴰ_ (fᴰ , gᴰ) (fᴰ' , gᴰ') = fᴰ Cᴰ.⋆ᴰ fᴰ' , gᴰ Dᴰ.⋆ᴰ gᴰ'
  _×Cᴰ_ .⋆IdLᴰ _ =
    ΣPathP (
      ΣPathP ((C.⋆IdL _) , (D.⋆IdL _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdLᴰ _)))
  _×Cᴰ_ .⋆IdRᴰ _ =
    ΣPathP (
      ΣPathP ((C.⋆IdR _) , (D.⋆IdR _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdRᴰ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdRᴰ _)))
  _×Cᴰ_ .⋆Assocᴰ _ _ _ =
    ΣPathP (
      ΣPathP ((C.⋆Assoc _ _ _) , (D.⋆Assoc _ _ _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assocᴰ _ _ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆Assocᴰ _ _ _)))
  _×Cᴰ_ .isSetHomᴰ = isSet× Cᴰ.isSetHomᴰ Dᴰ.isSetHomᴰ

module _
  {C : Category Cob CHom-ℓ}{Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
  (Cᴰ : SmallFibersCategoryᴰ C Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ)
  {D : Category Dob DHom-ℓ} {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ

  _×CᴰSF_ : SmallFibersCategoryᴰ (C ×C D) _
            (λ (c , d) → Cobᴰ c × Dobᴰ d)
            _
  _×CᴰSF_ .Hom[_][_,_] (f , g) (liftω (c , d)) (liftω (c' , d')) =
    Cᴰ.Hom[ f ][ liftω c , liftω c' ] × Dᴰ.Hom[ g ][ liftω d , liftω d' ]
  _×CᴰSF_ .idᴰ = Cᴰ.idᴰ , Dᴰ.idᴰ
  _×CᴰSF_ ._⋆ᴰ_ (fᴰ , gᴰ) (fᴰ' , gᴰ') = fᴰ Cᴰ.⋆ᴰ fᴰ' , gᴰ Dᴰ.⋆ᴰ gᴰ'
  _×CᴰSF_ .⋆IdLᴰ _ =
    ΣPathP (
      ΣPathP ((C.⋆IdL _) , (D.⋆IdL _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdLᴰ _)))
  _×CᴰSF_ .⋆IdRᴰ _ =
    ΣPathP (
      ΣPathP ((C.⋆IdR _) , (D.⋆IdR _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdRᴰ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆IdRᴰ _)))
  _×CᴰSF_ .⋆Assocᴰ _ _ _ =
    ΣPathP (
      ΣPathP ((C.⋆Assoc _ _ _) , (D.⋆Assoc _ _ _)) ,
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assocᴰ _ _ _) ,
              (Dᴰ.rectify $ Dᴰ.≡out $ Dᴰ.⋆Assocᴰ _ _ _)))
  _×CᴰSF_ .isSetHomᴰ = isSet× Cᴰ.isSetHomᴰ Dᴰ.isSetHomᴰ

module _
  {C : Category Cob CHom-ℓ}{Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
  (Cᴰ : SmallFibersCategoryᴰ C Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ)
  {D : Category Dob DHom-ℓ} {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
    module D = CategoryNotation D
    module Dᴰ = Categoryᴰ Dᴰ
    module Cᴰ×Dᴰ = CategoryᴰNotation (Cᴰ ×CᴰSF Dᴰ)

  open Functor
  -- It's a bit of a pain that this isn't definitional
  ×CᴰSFFiber→ProductOfFibers :
    ∀ {c} {d} → Functor Cᴰ×Dᴰ.v[ c , d ] (Cᴰ.v[ c ] ×C Dᴰ.v[ d ])
  ×CᴰSFFiber→ProductOfFibers .F-ob = λ z → liftω (z .Liftω.lowerω .fst) , liftω (z .Liftω.lowerω .snd)
  ×CᴰSFFiber→ProductOfFibers .F-hom = λ z → z
  ×CᴰSFFiber→ProductOfFibers .F-id = refl
  ×CᴰSFFiber→ProductOfFibers .F-seq _ _ = refl

  ProductOfFibers→×CᴰSFFiber :
    ∀ {c} {d} → Functor (Cᴰ.v[ c ] ×C Dᴰ.v[ d ]) Cᴰ×Dᴰ.v[ c , d ]
  ProductOfFibers→×CᴰSFFiber .F-ob = λ z → liftω (z .fst .Liftω.lowerω , z .snd .Liftω.lowerω)
  ProductOfFibers→×CᴰSFFiber .F-hom = λ z → z
  ProductOfFibers→×CᴰSFFiber .F-id = refl
  ProductOfFibers→×CᴰSFFiber .F-seq _ _ = refl

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
