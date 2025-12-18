{-- This file contains some utilities for reasoning
 -- about the HLevels of morphisms in displayed categories.
 --}
module Cubical.Categories.Displayed.HLevels.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Reasoning as Reasoning

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (isPropHom : hasPropHoms Cᴰ) where
  open Category
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module RCᴰ = Reasoning Cᴰ

  opaque
    propHomsFiller :
      ∀ {x y}{xᴰ yᴰ}
        {f g : C [ x , y ]}
        (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
        (p : f ≡ g)
        gᴰ
      → fᴰ Cᴰ.≡[ p ] gᴰ
    propHomsFiller fᴰ p gᴰ = toPathP (isPropHom _ _ _ _ _)

module _
       {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
       {F : Functor C D}
       {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
       {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Category
  open Functor
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  module _
    (propHoms : hasPropHoms Dᴰ)
    (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
    (F-homᴰ : {x y : C .ob}
      {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
       → Cᴰ [ f ][ xᴰ , yᴰ ] → Dᴰ [ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ])
    where
    opaque
      Fhomᴰ : {x y : C .ob}
        {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
         → Cᴰ [ f ][ xᴰ , yᴰ ] → Dᴰ [ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]
      Fhomᴰ = F-homᴰ
    mkOpaquePropHomsFunctor : Functorᴰ F Cᴰ Dᴰ
    mkOpaquePropHomsFunctor .Functorᴰ.F-obᴰ = F-obᴰ
    mkOpaquePropHomsFunctor .Functorᴰ.F-homᴰ = Fhomᴰ
    mkOpaquePropHomsFunctor .Functorᴰ.F-idᴰ = propHomsFiller Dᴰ propHoms _ _ _
    mkOpaquePropHomsFunctor .Functorᴰ.F-seqᴰ = λ _ _ → propHomsFiller Dᴰ propHoms _ _ _
