module Cubical.Categories.LocallySmall.Displayed.Functor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties

open Σω
open CatIso
open CatIsoᴰ
open Functor

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

module _
  {C : SmallCategory ℓC ℓC'} {D : SmallCategory ℓD ℓD'} where
  private
    module C = SmallCategory C
    module D = SmallCategory D
  module _ {F : Functor (C.cat) (D.cat)}
    {Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ'}
    {ℓDᴰ ℓDᴰ'}
    {Dᴰ : SmallCategoryᴰ D ℓDᴰ ℓDᴰ'}
    where

    private
      module Cᴰ = SmallCategoryᴰ Cᴰ
      module ∫Cᴰ = SmallCategory Cᴰ.∫Csmall
      module Dᴰ = SmallCategoryᴰ Dᴰ
      module ∫Dᴰ = SmallCategory Dᴰ.∫Csmall

    module _ (Fᴰ : Functorᴰ F (Cᴰ.catᴰ) (Dᴰ.catᴰ)) where
      private
        module F = FunctorNotation F
        module Fᴰ = Functorᴰ Fᴰ

      ∫Fsmall' : Functor ∫Cᴰ.cat ∫Dᴰ.cat
      ∫Fsmall' .F-ob (liftω (x , xᴰ)) =
        liftω (F.F-ob (liftω x) .Liftω.lowerω ,
               Fᴰ.F-obᴰ (liftω xᴰ) .Liftω.lowerω)
      ∫Fsmall' .F-hom (f , fᴰ) = F.F-hom f , Fᴰ.F-homᴰ fᴰ
      ∫Fsmall' .F-id = Fᴰ.F-idᴰ
      ∫Fsmall' .F-seq = λ f g → Fᴰ.F-seqᴰ (f .snd) (g .snd)

      open Categoryᴰ
      ∫Fsmall : Functor (∫C (Cᴰ.catᴰ)) (∫C (Dᴰ.catᴰ))
      ∫Fsmall .F-ob  = λ z → F.F-ob (z .Σω.fst) , Fᴰ.F-obᴰ (z .Σω.snd)
      ∫Fsmall .F-hom = λ z → F.F-hom (z .fst) , Fᴰ.F-homᴰ (z .snd)
      ∫Fsmall .F-id = Fᴰ.F-idᴰ
      ∫Fsmall .F-seq = λ f g → Fᴰ.F-seqᴰ (f .snd) (g .snd)

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

module _ {C : Category Cob CHom-ℓ}{D : Category Dob DHom-ℓ}
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (c : Cob)
  where
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Dᴰ = CategoryᴰNotation Dᴰ
    module F = FunctorNotation F
    module Fᴰ = FunctorᴰNotation Fᴰ

  Fv : Functor Cᴰ.v[ c ] Dᴰ.v[ F.F-ob c ]
  Fv .F-ob = Fᴰ.F-obᴰ
  Fv .F-hom fᴰ = Dᴰ.reind F.F-id $ Fᴰ.F-homᴰ fᴰ
  Fv .F-id =
    Dᴰ.rectify $ Dᴰ.≡out $
      (sym $ Dᴰ.reind-filler _ _)
      ∙ Fᴰ.F-idᴰ
  Fv .F-seq fᴰ gᴰ =
    Dᴰ.rectify $ Dᴰ.≡out $
      (sym $ Dᴰ.reind-filler _ _)
      ∙ Fᴰ.F-homᴰ⟨ (sym $ Cᴰ.reind-filler _ _) ⟩
      ∙ Fᴰ.F-seqᴰ _ _
      ∙ Dᴰ.⟨ Dᴰ.reind-filler _ _ ⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩
      ∙ Dᴰ.reind-filler _ _
