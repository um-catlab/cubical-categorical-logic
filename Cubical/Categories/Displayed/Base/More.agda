{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Base.More where


open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  open Functor

  Fst :  Functor (∫C Cᴰ) C
  Fst .F-ob = fst
  Fst .F-hom = fst
  Fst .F-id = refl
  Fst .F-seq =
    λ f g → cong {x = f ⋆⟨ ∫C Cᴰ ⟩ g} fst refl

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Category
  open Categoryᴰ Cᴰ

  base-path-irr : ∀ {x y xᴰ yᴰ} {f g : C [ x , y ]}
                → {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
                → {p : f ≡ g}
                → {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
                → {q : f ≡ g}
                → fᴰ ≡[ p ] gᴰ
                → fᴰ ≡[ q ] gᴰ
  base-path-irr {fᴰ = fᴰ}{p}{gᴰ}{q} = transport λ i →
    fᴰ ≡[ C .isSetHom _ _ p q i ] gᴰ
