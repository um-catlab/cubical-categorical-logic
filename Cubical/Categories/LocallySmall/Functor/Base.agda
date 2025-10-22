module Cubical.Categories.LocallySmall.Functor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Prod using (_×ω_; _,_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.LocallySmall.Base as LocallySmall
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Displayed.Base
open import Cubical.Categories.LocallySmall.Displayed.Properties

open CatIso
open CatIsoᴰ

record Functor (C : Category Cob CHom-ℓ) (D : Category Dob DHom-ℓ) : Typeω where
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
