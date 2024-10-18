{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
  isSetDepHomᴰ : ∀ {x y}{xᴰ yᴰ} →
    isSetDep (λ (f : C [ x , y ]) → Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
  isSetDepHomᴰ = isSet→isSetDep (λ f → Cᴰ.isSetHomᴰ)

  isSetHomᴰ' : ∀ {x y}{xᴰ}{yᴰ}
    {f g : C [ x , y ]} {p q : f ≡ g}
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
    (gᴰ : Cᴰ.Hom[ g ][ xᴰ , yᴰ ])
    (pᴰ : fᴰ Cᴰ.≡[ p ] gᴰ )
    (qᴰ : fᴰ Cᴰ.≡[ q ] gᴰ )
    → ∀ i j → Cᴰ.Hom[  C.isSetHom f g p q i j ][ xᴰ , yᴰ ]
  isSetHomᴰ' fᴰ gᴰ pᴰ qᴰ i j = isSetDepHomᴰ fᴰ gᴰ pᴰ qᴰ (C.isSetHom _ _ _ _) i j
