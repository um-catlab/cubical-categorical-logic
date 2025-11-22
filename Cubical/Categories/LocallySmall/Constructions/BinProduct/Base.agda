module Cubical.Categories.LocallySmall.Constructions.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Prod using (_×ω_; _,_)

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor.Base

open Category
open Σω

module _
  (C : Category Cob CHom-ℓ)
  (D : Category Dob DHom-ℓ)
  where
  private
    module C = Category C
    module D = Category D

  _×C_ : Category (Σω[ c ∈ Cob ] Dob) _
  _×C_ .Hom[_,_] (c , d) (c' , d') =
    C.Hom[ c , c' ] × D.Hom[ d , d' ]
  _×C_ .id = C.id , D.id
  _×C_ ._⋆_ = λ f g → f .fst C.⋆ g .fst , f .snd D.⋆ g .snd
  _×C_ .⋆IdL f = ≡-× (C.⋆IdL (f .fst)) (D.⋆IdL (f .snd))
  _×C_ .⋆IdR f = ≡-× (C.⋆IdR (f .fst)) (D.⋆IdR (f .snd))
  _×C_ .⋆Assoc f g h =
    ≡-×
      (C.⋆Assoc (f .fst) (g .fst) (h .fst))
      (D.⋆Assoc (f .snd) (g .snd) (h .snd))
  _×C_ .isSetHom = isSet× C.isSetHom D.isSetHom

  open Functor
  π₁ : Functor _×C_ C
  π₁ .F-ob = λ z → z .fst
  π₁ .F-hom = λ z → z .fst
  π₁ .F-id = refl
  π₁ .F-seq _ _ = refl

  π₂ : Functor _×C_ D
  π₂ .F-ob = λ z → z .snd
  π₂ .F-hom = λ z → z .snd
  π₂ .F-id = refl
  π₂ .F-seq _ _ = refl

module _
  (C : SmallCategory ℓC ℓC')
  (D : SmallCategory ℓD ℓD')
  where
  private
    module C = SmallCategory C
    module D = SmallCategory D

  open SmallCategory
  _×Csmall_ : SmallCategory _ _
  _×Csmall_ .small-ob = C.small-ob × D.small-ob
  _×Csmall_ .cat .Hom[_,_] (liftω (c , d)) (liftω (c' , d')) =
    C.Hom[ liftω c , liftω c' ] × D.Hom[ liftω d , liftω d' ]
  _×Csmall_ .cat .id = C.id , D.id
  _×Csmall_ .cat ._⋆_ = λ f g → f .fst C.⋆ g .fst , f .snd D.⋆ g .snd
  _×Csmall_ .cat .⋆IdL f = ≡-× (C.⋆IdL (f .fst)) (D.⋆IdL (f .snd))
  _×Csmall_ .cat .⋆IdR f = ≡-× (C.⋆IdR (f .fst)) (D.⋆IdR (f .snd))
  _×Csmall_ .cat .⋆Assoc f g h =
    ≡-×
      (C.⋆Assoc (f .fst) (g .fst) (h .fst))
      (D.⋆Assoc (f .snd) (g .snd) (h .snd))
  _×Csmall_ .cat .isSetHom = isSet× C.isSetHom D.isSetHom

  open Functor
  π₁small : Functor (_×Csmall_ .cat) C.cat
  π₁small .F-ob = mapω fst
  π₁small .F-hom = fst
  π₁small .F-id = refl
  π₁small .F-seq _ _ = refl

  π₂small : Functor (_×Csmall_ .cat) D.cat
  π₂small .F-ob = mapω snd
  π₂small .F-hom = snd
  π₂small .F-id = refl
  π₂small .F-seq _ _ = refl
