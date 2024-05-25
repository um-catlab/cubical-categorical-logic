{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.HLevels.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
  renaming (Fst to FstBP ; Snd to SndBP)
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _
       {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
       {F : Functor C D}
       {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
       where
  open Category
  open Functor
  private
    module Dᴰ = Categoryᴰ Dᴰ
  mkPropHomsSection :
    (propHoms : hasPropHoms Dᴰ)
      → (F-obᴰ  : (x : C .ob) → Dᴰ.ob[ F .F-ob x ])
      → (F-homᴰ : {x y : C .ob}
        (f : C [ x , y ]) → Dᴰ [ F .F-hom f ][ F-obᴰ x , F-obᴰ y ])
      → Section F Dᴰ
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-obᴰ = F-obᴰ
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-homᴰ = F-homᴰ
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-idᴰ =
    isProp→PathP (λ i → propHoms _ _ _) _ _
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-seqᴰ _ _ =
    isProp→PathP (λ i → propHoms _ _ _) _ _

  mkContrHomsSection :
    (contrHoms : hasContrHoms Dᴰ)
      → (F-obᴰ  : (x : C .ob) → Dᴰ.ob[ F .F-ob x ])
      → Section F Dᴰ
  mkContrHomsSection contrHoms F-obᴰ = mkPropHomsSection
    (hasContrHoms→hasPropHoms Dᴰ contrHoms)
    F-obᴰ
      λ {x}{y} f → contrHoms (F .F-hom f) (F-obᴰ x) (F-obᴰ y) .fst

  module _ {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
    private
      module Cᴰ = Categoryᴰ Cᴰ
    -- Alternate version: maybe Dᴰ.Hom[_][_,_] isn't always
    -- contractible, but it is in the image of F-obᴰ
    mkContrHomsFunctor'
      : (F-obᴰ  : {x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
      → (F-homᴰ : {x y : C .ob}
        {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      → Cᴰ [ f ][ xᴰ , yᴰ ]
      → isContr (Dᴰ [ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]))
      → Functorᴰ F Cᴰ Dᴰ
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-obᴰ = F-obᴰ
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-homᴰ fᴰ = F-homᴰ fᴰ .fst
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-idᴰ =
      symP (toPathP (isProp→PathP (λ i → isContr→isProp (F-homᴰ Cᴰ.idᴰ)) _ _))
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ =
      symP (toPathP (isProp→PathP
        (λ i → isContr→isProp (F-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ))) _ _))
