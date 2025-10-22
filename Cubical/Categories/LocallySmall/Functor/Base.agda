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

record Functorᴰ {C : Category Cob CHom-ℓ}{D : Category Dob DHom-ℓ}
  (F : Functor C D)
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  (Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ)
  : Typeω where
  no-eta-equality
  constructor functorᴰ
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Dᴰ = CategoryᴰNotation Dᴰ
    module F = FunctorNotation F
  field
    F-obᴰ : ∀ {x} → Cobᴰ x → Dobᴰ (F.F-ob x)
    F-homᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
      (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
      → Dᴰ.Hom[ F.F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]
    F-idᴰ : ∀ {x}{xᴰ : Cobᴰ x}
      → F-homᴰ (Cᴰ.idᴰ {xᴰ = xᴰ}) Dᴰ.∫≡ Dᴰ.idᴰ
    F-seqᴰ : ∀ {x y z xᴰ yᴰ zᴰ}
      {f : C.Hom[ x , y ]}
      {g : C.Hom[ y , z ]}
      (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
      (gᴰ : Cᴰ.Hom[ g ][ yᴰ , zᴰ ])
      → F-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ) Dᴰ.∫≡ F-homᴰ fᴰ Dᴰ.⋆ᴰ F-homᴰ gᴰ
  F-homᴰ⟨_⟩ : ∀ {x y xᴰ yᴰ}{f g : C.Hom[ x , y ]}
      {fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]}
      {gᴰ : Cᴰ.Hom[ g ][ xᴰ , yᴰ ]}
      (fᴰ≡gᴰ : fᴰ Cᴰ.∫≡ gᴰ)
      → F-homᴰ fᴰ Dᴰ.∫≡ F-homᴰ gᴰ
  F-homᴰ⟨ fᴰ≡gᴰ ⟩ i = (F.F-hom $ fᴰ≡gᴰ i .fst) , (F-homᴰ $ fᴰ≡gᴰ i .snd)

  F-isoᴰ : ∀ {x y xᴰ yᴰ}{f : C.ISOC.Hom[ x , y ]}
      (fᴰ : Cᴰ.ISOCᴰ.Hom[ f ][ xᴰ , yᴰ ])
      → Dᴰ.ISOCᴰ.Hom[ F.F-ISO.F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]
  F-isoᴰ fᴰ .funᴰ = F-homᴰ (fᴰ .funᴰ)
  F-isoᴰ fᴰ .invᴰ = F-homᴰ (fᴰ .invᴰ)
  F-isoᴰ fᴰ .secᴰ = sym (F-seqᴰ (fᴰ .invᴰ) (fᴰ .funᴰ)) ∙ F-homᴰ⟨ fᴰ .secᴰ ⟩ ∙ F-idᴰ
  F-isoᴰ fᴰ .retᴰ = sym (F-seqᴰ (fᴰ .funᴰ) (fᴰ .invᴰ)) ∙ F-homᴰ⟨ fᴰ .retᴰ ⟩ ∙ F-idᴰ

  ∫F : Functor Cᴰ.∫C Dᴰ.∫C
  ∫F .F-ob (x , xᴰ) = F.F-ob x , F-obᴰ xᴰ
  ∫F .F-hom (f , fᴰ) = F.F-hom f , F-homᴰ fᴰ
  ∫F .F-id = F-idᴰ
  ∫F .F-seq (_ , fᴰ) (_ , gᴰ) = F-seqᴰ fᴰ gᴰ

open Functorᴰ
module _ {C : Category Cob CHom-ℓ}{D : Category Dob DHom-ℓ}
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  where

  private
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Dᴰ = CategoryᴰNotation Dᴰ
    module F = FunctorNotation F

  F-Isoᴰ : (Fᴰ : Functorᴰ F Cᴰ Dᴰ) → Functorᴰ F.F-ISO Cᴰ.ISOCᴰ Dᴰ.ISOCᴰ
  F-Isoᴰ Fᴰ .F-obᴰ = Fᴰ .F-obᴰ
  F-Isoᴰ Fᴰ .F-homᴰ = F-isoᴰ Fᴰ
  F-Isoᴰ Fᴰ .F-idᴰ = Dᴰ.ISOCᴰ≡ (Fᴰ .F-idᴰ)
  F-Isoᴰ Fᴰ .F-seqᴰ fᴰ gᴰ = Dᴰ.ISOCᴰ≡ (Fᴰ .F-seqᴰ (fᴰ .funᴰ) (gᴰ .funᴰ))

  module FunctorᴰNotation (Fᴰ : Functorᴰ F Cᴰ Dᴰ) where
    open Functor (∫F Fᴰ) public -- should this be FunctorNotation?
    open Functorᴰ Fᴰ public

    F-ISOᴰ = F-Isoᴰ Fᴰ
    module F-ISOᴰ = Functorᴰ F-ISOᴰ

Functorⱽ : {C : Category Cob CHom-ℓ}
           (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)(Dᴰ : Categoryᴰ C Dobᴰ DHom-ℓᴰ)
  → Typeω
Functorⱽ = Functorᴰ idF

idFᴰ : ∀ {C : Category Cob CHom-ℓ}  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  → Functorⱽ Cᴰ Cᴰ
idFᴰ .F-obᴰ = λ z → z
idFᴰ .F-homᴰ = λ fᴰ → fᴰ
idFᴰ .F-idᴰ = refl
idFᴰ .F-seqᴰ fᴰ gᴰ = refl

_∘Fᴰ_ : ∀ {C : Category Cob CHom-ℓ}{Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {D : Category Dob DHom-ℓ}{Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  {E : Category Eob EHom-ℓ}{Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ}
  {G : Functor D E}
  {F : Functor C D}
  (Gᴰ : Functorᴰ G Dᴰ Eᴰ)
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  → Functorᴰ (G ∘F F) Cᴰ Eᴰ
Gᴰ ∘Fᴰ Fᴰ = functorᴰ
  (λ xᴰ → Gᴰ.F-obᴰ (Fᴰ.F-obᴰ xᴰ))
  (λ fᴰ → Gᴰ.F-homᴰ (Fᴰ.F-homᴰ fᴰ))
  (Gᴰ.F-homᴰ⟨ Fᴰ.F-idᴰ ⟩ ∙ Gᴰ.F-idᴰ)
  λ fᴰ gᴰ → Gᴰ.F-homᴰ⟨ Fᴰ.F-seqᴰ fᴰ gᴰ ⟩ ∙ Gᴰ.F-seqᴰ (Fᴰ.F-homᴰ fᴰ) (Fᴰ.F-homᴰ gᴰ)
  where
    module Gᴰ = Functorᴰ Gᴰ
    module Fᴰ = Functorᴰ Fᴰ
