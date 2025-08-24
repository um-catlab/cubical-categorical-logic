module Cubical.Categories.Displayed.Constructions.StructureOver.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.StructureOver

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _
       {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
       (F : Functor C D)
       (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (Qᴰ : StructureOver D ℓDᴰ ℓDᴰ') where
  open Category
  open Functor
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Qᴰ = StructureOver Qᴰ

  module _
       (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Qᴰ.ob[ F .F-ob x ])
       (F-homᴰ : {x y : C .ob} {f : C [ x , y ]}
       {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
        → Cᴰ.Hom[ f ][ xᴰ , yᴰ ]
        → Qᴰ.Hom[ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]) where

    intro : Functorᴰ F Cᴰ (StructureOver→Catᴰ Qᴰ)
    intro =
      mkPropHomsFunctor (hasPropHomsStructureOver Qᴰ) F-obᴰ F-homᴰ
