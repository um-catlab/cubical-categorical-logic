-- The displayed collage of a displayed profunctor.
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Displayed.FromProf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒)
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Profunctor
import Cubical.Categories.Displayed.Presheaf.Base as Curried
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.FromProf

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

module _ {C : Category ℓ ℓ'} {V : Category ℓ ℓ'}
  {O : Profunctor C V ℓ'}
  {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'} {Vᴰ : Categoryᴰ V ℓᴰ ℓᴰ'}
  (Oᴰ : Profunctorᴰ O Cᴰ Vᴰ ℓᴰ') where
  open Categoryᴰ
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Vᴰ = Categoryᴰ Vᴰ
    module Base = Categoryᴰ (Prof→CBPV O)

    Obᴰ : ∀ {k} → Base.ob[ k ] → Type ℓᴰ
    Obᴰ {𝓥} A = Vᴰ.ob[ A ]
    Obᴰ {𝓒} B = Cᴰ.ob[ B ]

    Hetᴰ : ∀ {A B} → RelatorNotation.Het[_,_] (CurriedToBifunctorL O) A B
      → Vᴰ.ob[ A ] → Cᴰ.ob[ B ] → Type ℓᴰ'
    Hetᴰ p Aᴰ Bᴰ = Pᴰ.p[ p ][ Aᴰ ]
      where module Pᴰ = Curried.PresheafᴰNotation (Functorᴰ.F-obᴰ Oᴰ Bᴰ)

    isSetHetᴰ : ∀ {A B} {p : RelatorNotation.Het[_,_] (CurriedToBifunctorL O) A B}
      {Aᴰ : Vᴰ.ob[ A ]} {Bᴰ : Cᴰ.ob[ B ]} → isSet (Hetᴰ p Aᴰ Bᴰ)
    isSetHetᴰ {Bᴰ = Bᴰ} = Pᴰ.isSetPshᴰ
      where module Pᴰ = Curried.PresheafᴰNotation (Functorᴰ.F-obᴰ Oᴰ Bᴰ)

    Homᴰ : ∀ {k k'} {k≤ : KIND [ k , k' ]}
      {A : Base.ob[ k ]} {B : Base.ob[ k' ]}
      → Categoryᴰ.Hom[_][_,_] (Prof→CBPV O) k≤ A B
      → Obᴰ A → Obᴰ B → Type ℓᴰ'
    Homᴰ {𝓥} {𝓥} f Aᴰ Bᴰ = Vᴰ [ f ][ Aᴰ , Bᴰ ]
    Homᴰ {𝓥} {𝓒} p Aᴰ Bᴰ = Hetᴰ p Aᴰ Bᴰ
    Homᴰ {𝓒} {𝓒} f Aᴰ Bᴰ = Cᴰ [ f ][ Aᴰ , Bᴰ ]

  -- Feels like we shouldn't have all of these rectifies...
  Prof→CBPVᴰ : CBPVCatᴰ (Prof→CBPV O) ℓᴰ ℓᴰ'
  Prof→CBPVᴰ .ob[_] (k , A) = Obᴰ {k} A
  Prof→CBPVᴰ .Hom[_][_,_] (k≤ , f) Aᴰ Bᴰ = Homᴰ {k≤ = k≤} f Aᴰ Bᴰ
  Prof→CBPVᴰ .idᴰ {𝓥 , _} = Vᴰ.idᴰ
  Prof→CBPVᴰ .idᴰ {𝓒 , _} = Cᴰ.idᴰ
  Prof→CBPVᴰ ._⋆ᴰ_ {x = (𝓥 , _)} {y = (𝓥 , _)} {z = (𝓥 , _)} = Vᴰ._⋆ᴰ_
  Prof→CBPVᴰ ._⋆ᴰ_ {x = (𝓥 , _)} {y = (𝓥 , _)} {z = (𝓒 , _)}
    {zᴰ = zᴰ} fᴰ gᴰ = Pᴰ._⋆ᴰ_ fᴰ gᴰ
    where module Pᴰ = Curried.PresheafᴰNotation (Functorᴰ.F-obᴰ Oᴰ zᴰ)
  Prof→CBPVᴰ ._⋆ᴰ_ {x = (𝓥 , _)} {y = (𝓒 , _)} {z = (𝓒 , _)}
    {f = (_ , f)} {xᴰ = xᴰ} fᴰ gᴰ =
      Functorᴰ.F-homᴰ Oᴰ gᴰ .NatTransᴰ.N-obᴰ xᴰ f fᴰ
  Prof→CBPVᴰ ._⋆ᴰ_ {x = (𝓒 , _)} {y = (𝓒 , _)} {z = (𝓒 , _)} = Cᴰ._⋆ᴰ_
  Prof→CBPVᴰ .⋆IdLᴰ {x = (𝓥 , _)} {y = (𝓥 , _)} = Vᴰ.⋆IdLᴰ
  Prof→CBPVᴰ .⋆IdLᴰ {x = (𝓥 , _)} {y = (𝓒 , _)} {yᴰ = yᴰ} fᴰ =
    Pᴰ.rectify (Pᴰ.⋆IdLᴰ fᴰ)
    where module Pᴰ = Curried.PresheafᴰNotation (Functorᴰ.F-obᴰ Oᴰ yᴰ)
  Prof→CBPVᴰ .⋆IdLᴰ {x = (𝓒 , _)} {y = (𝓒 , _)} = Cᴰ.⋆IdLᴰ

  Prof→CBPVᴰ .⋆IdRᴰ {x = (𝓥 , _)} {y = (𝓥 , _)} = Vᴰ.⋆IdRᴰ
  Prof→CBPVᴰ .⋆IdRᴰ {x = (𝓥 , _)} {y = (𝓒 , _)}
    {f = (_ , f)} {xᴰ = xᴰ} {yᴰ = yᴰ} fᴰ =
    Pᴰ.rectify
      (λ i → Functorᴰ.F-idᴰ Oᴰ i .NatTransᴰ.N-obᴰ xᴰ f fᴰ)
    where module Pᴰ = Curried.PresheafᴰNotation (Functorᴰ.F-obᴰ Oᴰ yᴰ)
  Prof→CBPVᴰ .⋆IdRᴰ {x = (𝓒 , _)} {y = (𝓒 , _)} = Cᴰ.⋆IdRᴰ

  Prof→CBPVᴰ .⋆Assocᴰ {x = (𝓥 , _)} {y = (𝓥 , _)}
    {z = (𝓥 , _)} {w = (𝓥 , _)} = Vᴰ.⋆Assocᴰ
  Prof→CBPVᴰ .⋆Assocᴰ {x = (𝓥 , _)} {y = (𝓥 , _)}
    {z = (𝓥 , _)} {w = (𝓒 , _)} {wᴰ = wᴰ} fᴰ gᴰ hᴰ =
    Pᴰ.rectify (Pᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ)
    where module Pᴰ = Curried.PresheafᴰNotation (Functorᴰ.F-obᴰ Oᴰ wᴰ)
  Prof→CBPVᴰ .⋆Assocᴰ {x = (𝓥 , _)} {y = (𝓥 , _)}
    {z = (𝓒 , _)} {w = (𝓒 , _)} {g = (_ , g)}
    {wᴰ = wᴰ} fᴰ gᴰ hᴰ =
    Pᴰ.rectify
      (λ i → Functorᴰ.F-homᴰ Oᴰ hᴰ .NatTransᴰ.N-homᴰ fᴰ i g gᴰ)
    where module Pᴰ = Curried.PresheafᴰNotation (Functorᴰ.F-obᴰ Oᴰ wᴰ)
  Prof→CBPVᴰ .⋆Assocᴰ {x = (𝓥 , _)} {y = (𝓒 , _)}
    {z = (𝓒 , _)} {w = (𝓒 , _)} {f = (_ , f)}
    {xᴰ = xᴰ} {wᴰ = wᴰ} fᴰ gᴰ hᴰ =
    Pᴰ.rectify
      (λ i → Functorᴰ.F-seqᴰ Oᴰ gᴰ hᴰ (~ i) .NatTransᴰ.N-obᴰ xᴰ f fᴰ)
    where module Pᴰ = Curried.PresheafᴰNotation (Functorᴰ.F-obᴰ Oᴰ wᴰ)
  Prof→CBPVᴰ .⋆Assocᴰ {x = (𝓒 , _)} {y = (𝓒 , _)}
    {z = (𝓒 , _)} {w = (𝓒 , _)} = Cᴰ.⋆Assocᴰ
  Prof→CBPVᴰ .isSetHomᴰ {x = (𝓥 , _)} {y = (𝓥 , _)} = Vᴰ.isSetHomᴰ
  Prof→CBPVᴰ .isSetHomᴰ {x = (𝓥 , _)} {y = (𝓒 , _)} = isSetHetᴰ
  Prof→CBPVᴰ .isSetHomᴰ {x = (𝓒 , _)} {y = (𝓒 , _)} = Cᴰ.isSetHomᴰ
