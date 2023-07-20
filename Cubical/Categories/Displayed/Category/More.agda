{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Category.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  open Categoryᴰ D
  base-path-irr : ∀ {x y xᴰ yᴰ} {f g : C [ x , y ]}
                → {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
                → {p : f ≡ g}
                → {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
                → {q : f ≡ g}
                → fᴰ ≡[ p ] gᴰ
                → fᴰ ≡[ q ] gᴰ
  base-path-irr {fᴰ = fᴰ}{p}{gᴰ}{q} = transport λ i →
    fᴰ ≡[ C .isSetHom _ _ p q i ] gᴰ
