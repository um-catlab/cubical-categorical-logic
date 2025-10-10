module Cubical.Categories.LocallySmall.Functor where

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

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.Category as SmallCategory using (Category)
open import Cubical.Categories.Displayed.Base using (Categoryᴰ)
open import Cubical.Categories.LocallySmall as LocallySmall

private
  variable
    ℓ ℓ' ℓ1 ℓ2 ℓw ℓx ℓy ℓz ℓC ℓC' : Level
    ℓᴰ ℓᴰ' ℓ1ᴰ ℓ2ᴰ ℓwᴰ ℓxᴰ ℓyᴰ ℓzᴰ ℓCᴰ ℓCᴰ' : Level

    Cob Dob Eob : Typeω
    Cobᴰ : Cob → Typeω
    Dobᴰ : Dob → Typeω
    Eobᴰ : Eob → Typeω

open CatIso
open CatIsoᴰ

record Functor (C : LocallySmallCategory Cob) (D : LocallySmallCategory Dob) : Typeω where
  private
    module C = LocallySmallCategoryNotation C
    module D = LocallySmallCategoryNotation D
  field
    F-ob : Cob → Dob
    F-hom : ∀ {x y} → C.Hom[ x , y ] → D.Hom[ F-ob x , F-ob y ]
    F-id : ∀ {x} → F-hom (C.id {x}) ≡ D.id
    F-seq : ∀ {x y z}
      (f : C.Hom[ x , y ])
      (g : C.Hom[ y , z ])
      → F-hom (f C.⋆ g) ≡ F-hom f D.⋆ F-hom g
  -- TODO: this is functoriality on a displayed category of paths worth defining?
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

idF : ∀ {C : LocallySmallCategory Cob} → Functor C C
idF .F-ob = λ z → z
idF .F-hom = λ z → z
idF .F-id = refl
idF .F-seq f g = refl

_∘F_ : ∀ {C : LocallySmallCategory Cob}{D : LocallySmallCategory Dob}{E : LocallySmallCategory Eob}
  → Functor D E → Functor C D
  → Functor C E
(F ∘F G) .F-ob = λ z → F .F-ob (G .F-ob z)
(F ∘F G) .F-hom = λ z → F .F-hom (G .F-hom z)
(F ∘F G) .F-id = cong (F .F-hom) (G .F-id) ∙ F .F-id
(F ∘F G) .F-seq f g = cong (F .F-hom) (G .F-seq f g) ∙ F .F-seq (G .F-hom f) (G .F-hom g)

module _ {C : LocallySmallCategory Cob}{D : LocallySmallCategory Dob} where
  private
    module C = LocallySmallCategoryNotation C
    module D = LocallySmallCategoryNotation D
  F-Iso : (F : Functor C D) → Functor C.ISOC D.ISOC
  F-Iso F .F-ob = F .F-ob
  F-Iso F .F-hom = F-iso F
  F-Iso F .F-id = D.ISOC≡ (F .F-id)
  F-Iso F .F-seq f g = D.ISOC≡ (F .F-seq (f .CatIso.fun) (g .CatIso.fun))

  module FunctorNotation (F : Functor C D) where
    open Functor F public
    F-ISO = F-Iso F
    module F-ISO = Functor F-ISO

record Functorᴰ {C : LocallySmallCategory Cob}{D : LocallySmallCategory Dob}
  (F : Functor C D)
  (Cᴰ : LocallySmallCategoryᴰ C Cobᴰ)
  (Dᴰ : LocallySmallCategoryᴰ D Dobᴰ)
  : Typeω where
  private
    module C = LocallySmallCategoryNotation C
    module D = LocallySmallCategoryNotation D
    module Cᴰ = LocallySmallCategoryᴰNotation Cᴰ
    module Dᴰ = LocallySmallCategoryᴰNotation Dᴰ
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
module _ {C : LocallySmallCategory Cob}{D : LocallySmallCategory Dob}
  {F : Functor C D}
  {Cᴰ : LocallySmallCategoryᴰ C Cobᴰ}
  {Dᴰ : LocallySmallCategoryᴰ D Dobᴰ}
  where

  private
    module Cᴰ = LocallySmallCategoryᴰNotation Cᴰ
    module Dᴰ = LocallySmallCategoryᴰNotation Dᴰ
    module F = FunctorNotation F

  F-Isoᴰ : (Fᴰ : Functorᴰ F Cᴰ Dᴰ) → Functorᴰ F.F-ISO Cᴰ.ISOCᴰ Dᴰ.ISOCᴰ
  F-Isoᴰ Fᴰ .F-obᴰ = Fᴰ .F-obᴰ
  F-Isoᴰ Fᴰ .F-homᴰ = F-isoᴰ Fᴰ
  F-Isoᴰ Fᴰ .F-idᴰ = Dᴰ.ISOCᴰ≡ (Fᴰ .F-idᴰ)
  F-Isoᴰ Fᴰ .F-seqᴰ fᴰ gᴰ = Dᴰ.ISOCᴰ≡ (Fᴰ .F-seqᴰ (fᴰ .funᴰ) (gᴰ .funᴰ))

  module FunctorᴰNotation (Fᴰ : Functorᴰ F Cᴰ Dᴰ) where
    open Functor (∫F Fᴰ) public -- should this be FunctorNotation?
    F-ISOᴰ = F-Isoᴰ Fᴰ
    module F-ISOᴰ = Functorᴰ F-ISOᴰ

Functorⱽ : {C : LocallySmallCategory Cob} (Cᴰ : LocallySmallCategoryᴰ C Cobᴰ)(Dᴰ : LocallySmallCategoryᴰ C Dobᴰ)
  → Typeω
Functorⱽ = Functorᴰ idF

idFᴰ : ∀ {C : LocallySmallCategory Cob}  {Cᴰ : LocallySmallCategoryᴰ C Cobᴰ}
  → Functorⱽ Cᴰ Cᴰ
idFᴰ .F-obᴰ = λ z → z
idFᴰ .F-homᴰ = λ fᴰ → fᴰ
idFᴰ .F-idᴰ = refl
idFᴰ .F-seqᴰ fᴰ gᴰ = refl
