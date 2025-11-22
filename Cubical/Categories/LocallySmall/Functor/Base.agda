module Cubical.Categories.LocallySmall.Functor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit

import Cubical.Categories.Category as Small
import Cubical.Categories.Functor as SmallF

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base

open CatIso

record Functor (C : Category Cob CHom-ℓ) (D : Category Dob DHom-ℓ) : Typeω where
  -- no-eta-equality
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
  field
    F-ob : Cob → Dob
    F-hom : ∀ {x y} → C.Hom[ x , y ] → D.Hom[ F-ob x , F-ob y ]
    F-id : ∀ {x} → F-hom (C.id {x}) ≡ D.id
    F-seq : ∀ {x y z}
      (f : C.Hom[ x , y ])
      (g : C.Hom[ y , z ])
      → F-hom (f C.⋆ g) ≡ F-hom f D.⋆ F-hom g
  -- TODO: this is functoriality on a displayed category of paths. worth defining?
  F-hom⟨_⟩ : ∀ {x y} {f g : C.Hom[ x , y ]}
    → (f≡g : f ≡ g)
    → F-hom f ≡ F-hom g
  F-hom⟨_⟩ = cong F-hom

  F-iso : ∀ {x y} (f : C.ISOC.Hom[ x , y ]) → D.ISOC.Hom[ F-ob x , F-ob y ]
  F-iso f .CatIso.fun = F-hom (f .CatIso.fun)
  F-iso f .CatIso.inv = F-hom (f .CatIso.inv)
  F-iso f .CatIso.sec = sym (F-seq _ _) ∙ F-hom⟨ f .CatIso.sec ⟩ ∙ F-id
  F-iso f .CatIso.ret = sym (F-seq _ _) ∙ F-hom⟨ f .CatIso.ret ⟩ ∙ F-id

open Functor

idF : ∀ {C : Category Cob CHom-ℓ} → Functor C C
idF .F-ob = λ z → z
idF .F-hom = λ z → z
idF .F-id = refl
idF .F-seq f g = refl

_∘F_ : ∀ {C : Category Cob CHom-ℓ}{D : Category Dob DHom-ℓ}{E : Category Eob EHom-ℓ}
  → Functor D E → Functor C D
  → Functor C E
(F ∘F G) .F-ob = λ z → F .F-ob (G .F-ob z)
(F ∘F G) .F-hom = λ z → F .F-hom (G .F-hom z)
(F ∘F G) .F-id = cong (F .F-hom) (G .F-id) ∙ F .F-id
(F ∘F G) .F-seq f g = cong (F .F-hom) (G .F-seq f g) ∙ F .F-seq (G .F-hom f) (G .F-hom g)
infixr 30 _∘F_

module _ {C : Category Cob CHom-ℓ}{D : Category Dob DHom-ℓ} where
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
  F-Iso : (F : Functor C D) → Functor C.ISOC D.ISOC
  F-Iso F .F-ob = F .F-ob
  F-Iso F .F-hom = F-iso F
  F-Iso F .F-id = D.ISOC≡ (F .F-id)
  F-Iso F .F-seq f g = D.ISOC≡ (F .F-seq (f .CatIso.fun) (g .CatIso.fun))

  module FunctorNotation (F : Functor C D) where
    open Functor F public
    F-ISO = F-Iso F
    module F-ISO = Functor F-ISO

module _
  {C : Small.Category ℓC ℓC'}
  {D : Small.Category ℓD ℓD'}
  (F : SmallF.Functor C D)
  where
  private
    C' = mkSmallCategory C
    module C' = SmallCategory C'
    D' = mkSmallCategory D
    module D' = SmallCategory D'

  mkSmallFunctor : Functor C'.cat D'.cat
  mkSmallFunctor .F-ob = mapω (F .SmallF.Functor.F-ob)
  mkSmallFunctor .F-hom = F .SmallF.Functor.F-hom
  mkSmallFunctor .F-id = F .SmallF.Functor.F-id
  mkSmallFunctor .F-seq = F .SmallF.Functor.F-seq

module _
  {C : SmallCategory ℓC ℓC'}
  {D : SmallCategory ℓD ℓD'}
  where
  private
    module C = SmallCategory C
    module D = SmallCategory D
    C' = SmallLocallySmallCategory→SmallCategory C
    D' = SmallLocallySmallCategory→SmallCategory D
  module _ (F : Functor C.cat D.cat) where
    SmallLocallySmallFunctor→SmallFunctor :
      SmallF.Functor C' D'
    SmallLocallySmallFunctor→SmallFunctor .SmallF.Functor.F-ob =
      λ z → F-ob F (liftω z) .Liftω.lowerω
    SmallLocallySmallFunctor→SmallFunctor .SmallF.Functor.F-hom =
      F-hom F
    SmallLocallySmallFunctor→SmallFunctor .SmallF.Functor.F-id =
      F-id F
    SmallLocallySmallFunctor→SmallFunctor .SmallF.Functor.F-seq =
      F-seq F

module _
  {C : SmallCategory ℓC ℓC'} where
  private
    module C = SmallCategory C
    C' = SmallLocallySmallCategory→SmallCategory C

  open SmallCategory
  mkSmallCategoryF-intro :
    Functor C.cat (mkSmallCategory C' .cat)
  mkSmallCategoryF-intro .F-ob = λ z → z
  mkSmallCategoryF-intro .F-hom = λ z → z
  mkSmallCategoryF-intro .F-id = refl
  mkSmallCategoryF-intro .F-seq = λ _ _ → refl

  mkSmallCategoryF-elim :
    Functor (mkSmallCategory C' .cat) C.cat
  mkSmallCategoryF-elim .F-ob = λ z → z
  mkSmallCategoryF-elim .F-hom = λ z → z
  mkSmallCategoryF-elim .F-id = refl
  mkSmallCategoryF-elim .F-seq = λ _ _ → refl
