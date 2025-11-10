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
  (D : Category Dob DHom-ℓ) where
  private
    module C = SmallCategory C
    module D = CategoryNotation D
  _⊘_ : Category (C.small-ob ×ω Dob) _
  _⊘_ .Hom[_,_] (x , y) (x' , y') = C.Hom[ liftω x , liftω x' ] × D.Hom[ y , y' ]
  _⊘_ .id = C.id , D.id
  _⊘_ ._⋆_ (f , g) (f' , g') = (f C.⋆ f') , (g D.⋆ g')
  _⊘_ .⋆IdL (f , g) = ΣPathP (C.⋆IdL f , D.⋆IdL g)
  _⊘_ .⋆IdR (f , g) = ΣPathP (C.⋆IdR f , D.⋆IdR g)
  _⊘_ .⋆Assoc (f , g) (f' , g') (f'' , g'') = ΣPathP (C.⋆Assoc f f' f'' , D.⋆Assoc g g' g'')
  _⊘_ .isSetHom = isSet× C.isSetHom D.isSetHom

  open Functor
  ⊘π₁ : Functor _⊘_ C.cat
  ⊘π₁ .F-ob (c , d) = liftω c
  ⊘π₁ .F-hom (f , g) = f
  ⊘π₁ .F-id = refl
  ⊘π₁ .F-seq _ _ = refl

  ⊘π₂ : Functor _⊘_ D
  ⊘π₂ .F-ob (c , d) = d
  ⊘π₂ .F-hom (f , g) = g
  ⊘π₂ .F-id = refl
  ⊘π₂ .F-seq _ _ = refl


--   private
--     module ⊘ = LocallySmallCategoryNotation _⊘_
--   ⊘-iso : ∀ {x y x' y'}
--     → (f : SmallCategory.CatIso C x x')
--     → (g : D.ISOC.Hom[ y , y' ])
--     → ⊘.ISOC.Hom[ (x , y) , (x' , y') ]
--   ⊘-iso f g .CatIso.fun = (f .fst) , (g .CatIso.fun)
--   ⊘-iso f g .CatIso.inv = (f .snd .SmallCategory.isIso.inv) , (g .CatIso.inv)
--   ⊘-iso f g .CatIso.sec = ΣPathP (f .snd .SmallCategory.isIso.sec , g .CatIso.sec)
--   ⊘-iso f g .CatIso.ret = ΣPathP (f .snd .SmallCategory.isIso.ret , g .CatIso.ret)
