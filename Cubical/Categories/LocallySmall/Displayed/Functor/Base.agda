module Cubical.Categories.LocallySmall.Displayed.Functor.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

import Cubical.Categories.Category as Small
import Cubical.Categories.Functor as SmallF
import Cubical.Categories.Displayed.Base as Smallᴰ
import Cubical.Categories.Constructions.Fiber as Smallᴰ
import Cubical.Categories.Displayed.Functor as SmallFᴰ

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
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
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

-- If Functor has eta equality, then we don't need
-- these variants of compositions
module _ where
  _∘Fⱽᴰ_ : ∀ {C : Category Cob CHom-ℓ}{Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
    {D : Category Dob DHom-ℓ}{Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
    {Eᴰ : Categoryᴰ D Eobᴰ EHom-ℓᴰ}
    {F : Functor C D}
    (Gᴰ : Functorⱽ Dᴰ Eᴰ)
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    → Functorᴰ F Cᴰ Eᴰ
  Gᴰ ∘Fⱽᴰ Fᴰ = functorᴰ
    (λ {x} z → F-obᴰ Gᴰ (F-obᴰ Fᴰ z))
    (λ {x} {y} {xᴰ} {yᴰ} {f} fᴰ → F-homᴰ Gᴰ (F-homᴰ Fᴰ fᴰ))
    (Gᴰ.F-homᴰ⟨ Fᴰ.F-idᴰ ⟩ ∙ Gᴰ.F-idᴰ)
    λ fᴰ gᴰ → Gᴰ.F-homᴰ⟨ Fᴰ.F-seqᴰ fᴰ gᴰ ⟩ ∙ Gᴰ.F-seqᴰ (Fᴰ.F-homᴰ fᴰ) (Fᴰ.F-homᴰ gᴰ)
    where
      module Gᴰ = Functorᴰ Gᴰ
      module Fᴰ = Functorᴰ Fᴰ

  _∘Fᴰⱽ_ : ∀ {C : Category Cob CHom-ℓ}{Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
    {Dᴰ : Categoryᴰ C Dobᴰ DHom-ℓᴰ}
    {E : Category Eob EHom-ℓ}{Eᴰ : Categoryᴰ E Eobᴰ EHom-ℓᴰ}
    {G : Functor C E}
    (Gᴰ : Functorᴰ G Dᴰ Eᴰ)
    (Fᴰ : Functorⱽ Cᴰ Dᴰ)
    → Functorᴰ G Cᴰ Eᴰ
  Gᴰ ∘Fᴰⱽ Fᴰ = functorᴰ
    (λ {x} z → F-obᴰ Gᴰ (F-obᴰ Fᴰ z))
    (λ {x} {y} {xᴰ} {yᴰ} {f} fᴰ → F-homᴰ Gᴰ (F-homᴰ Fᴰ fᴰ))
    (Gᴰ.F-homᴰ⟨ Fᴰ.F-idᴰ ⟩ ∙ Gᴰ.F-idᴰ)
    λ fᴰ gᴰ → Gᴰ.F-homᴰ⟨ Fᴰ.F-seqᴰ fᴰ gᴰ ⟩ ∙ Gᴰ.F-seqᴰ (Fᴰ.F-homᴰ fᴰ) (Fᴰ.F-homᴰ gᴰ)
    where
      module Gᴰ = Functorᴰ Gᴰ
      module Fᴰ = Functorᴰ Fᴰ

  _∘Fⱽ_ : ∀ {C : Category Cob CHom-ℓ}{Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
    {Dᴰ : Categoryᴰ C Dobᴰ DHom-ℓᴰ}
    {Eᴰ : Categoryᴰ C Eobᴰ EHom-ℓᴰ}
    (Gᴰ : Functorⱽ Dᴰ Eᴰ)
    (Fᴰ : Functorⱽ Cᴰ Dᴰ)
    → Functorⱽ Cᴰ Eᴰ
  Gᴰ ∘Fⱽ Fᴰ = functorᴰ
    (λ {x} z → F-obᴰ Gᴰ (F-obᴰ Fᴰ z))
    (λ {x} {y} {xᴰ} {yᴰ} {f} fᴰ → F-homᴰ Gᴰ (F-homᴰ Fᴰ fᴰ))
    (Gᴰ.F-homᴰ⟨ Fᴰ.F-idᴰ ⟩ ∙ Gᴰ.F-idᴰ)
    λ fᴰ gᴰ → Gᴰ.F-homᴰ⟨ Fᴰ.F-seqᴰ fᴰ gᴰ ⟩ ∙ Gᴰ.F-seqᴰ (Fᴰ.F-homᴰ fᴰ) (Fᴰ.F-homᴰ gᴰ)
    where
      module Gᴰ = Functorᴰ Gᴰ
      module Fᴰ = Functorᴰ Fᴰ

module _
  {C : Small.Category ℓC ℓC'}
  {D : Small.Category ℓD ℓD'}
  {F : SmallF.Functor C D}
  {Cᴰ : Smallᴰ.Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {Dᴰ : Smallᴰ.Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : SmallFᴰ.Functorᴰ F Cᴰ Dᴰ)
  where
  private
    C' = mkSmallCategory C
    D' = mkSmallCategory D
    module C' = SmallCategory C'
    module D' = SmallCategory D'

    Cᴰ' = mkSmallCategoryᴰ Cᴰ
    Dᴰ' = mkSmallCategoryᴰ Dᴰ
    module Cᴰ' = SmallCategoryᴰ Cᴰ'
    module Dᴰ' = SmallCategoryᴰ Dᴰ'

  mkSmallFunctorᴰ : Functorᴰ (mkSmallFunctor F) Cᴰ'.catᴰ Dᴰ'.catᴰ
  mkSmallFunctorᴰ .F-obᴰ = λ z → liftω (SmallFᴰ.Functorᴰ.F-obᴰ Fᴰ (z .Liftω.lowerω))
  mkSmallFunctorᴰ .F-homᴰ = SmallFᴰ.Functorᴰ.F-homᴰ Fᴰ
  mkSmallFunctorᴰ .F-idᴰ = Dᴰ'.≡in $ SmallFᴰ.Functorᴰ.F-idᴰ Fᴰ
  mkSmallFunctorᴰ .F-seqᴰ _ _ = Dᴰ'.≡in $ SmallFᴰ.Functorᴰ.F-seqᴰ Fᴰ _ _

module _ {C : SmallCategory ℓC ℓC'} {D : SmallCategory ℓD ℓD'} where
  private
    module C = SmallCategory C
    module D = SmallCategory D
    C' = SmallLocallySmallCategory→SmallCategory C
    D' = SmallLocallySmallCategory→SmallCategory D
  module _ {F : Functor C.cat D.cat}
    {Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : SmallCategoryᴰ D ℓDᴰ ℓDᴰ'} where
    private
      module Cᴰ = SmallCategoryᴰ Cᴰ
      module Dᴰ = SmallCategoryᴰ Dᴰ
      Cᴰ' = SmallLocallySmallCategoryᴰ→SmallCategoryᴰ Cᴰ
      Dᴰ' = SmallLocallySmallCategoryᴰ→SmallCategoryᴰ Dᴰ
      module Dᴰ' = Smallᴰ.Fibers Dᴰ'
    module _ (Fᴰ : Functorᴰ F Cᴰ.catᴰ Dᴰ.catᴰ) where

      SmallLocallySmallFunctorᴰ→SmallFunctorᴰ :
        SmallFᴰ.Functorᴰ (SmallLocallySmallFunctor→SmallFunctor {C = C} {D = D} F) Cᴰ' Dᴰ'
      SmallLocallySmallFunctorᴰ→SmallFunctorᴰ .SmallFᴰ.Functorᴰ.F-obᴰ = λ z → F-obᴰ Fᴰ (liftω z) .Liftω.lowerω
      SmallLocallySmallFunctorᴰ→SmallFunctorᴰ .SmallFᴰ.Functorᴰ.F-homᴰ = F-homᴰ Fᴰ
      SmallLocallySmallFunctorᴰ→SmallFunctorᴰ .SmallFᴰ.Functorᴰ.F-idᴰ =
        Dᴰ'.rectify $ Dᴰ'.≡out (F-idᴰ Fᴰ)
      SmallLocallySmallFunctorᴰ→SmallFunctorᴰ .SmallFᴰ.Functorᴰ.F-seqᴰ _ _ =
        Dᴰ'.rectify $ Dᴰ'.≡out (F-seqᴰ Fᴰ _ _)
