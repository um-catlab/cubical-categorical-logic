{-
  A Magmoidᴰ is a Categoryᴰ without the equations
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Magmoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

-- Displayed categories with hom-sets
record Magmoidᴰ (C : Category ℓC ℓC') ℓCᴰ ℓCᴰ' : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))) where
  no-eta-equality
  open Category C
  field
    ob[_] : ob → Type ℓCᴰ
    Hom[_][_,_] : {x y : ob} → Hom[ x , y ] → ob[ x ] → ob[ y ] → Type ℓCᴰ'
    idᴰ : ∀ {x} {p : ob[ x ]} → Hom[ id ][ p , p ]
    _⋆ᴰ_ : ∀ {x y z} {f : Hom[ x , y ]} {g : Hom[ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f ⋆ g ][ xᴰ , zᴰ ]

  infixr 9 _⋆ᴰ_
  -- infixr 9 _∘ᴰ_
module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ

  module _ (idᴰ' : singl {A = ∀ {x} {p : Cᴰ.ob[ x ]} → Cᴰ.Hom[ C.id ][ p , p ]} Cᴰ.idᴰ)
           (⋆ᴰ' : singl {A = ∀ {x y z} {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]} {xᴰ yᴰ zᴰ} → Cᴰ.Hom[ f ][ xᴰ , yᴰ ] → Cᴰ.Hom[ g ][ yᴰ , zᴰ ] → Cᴰ.Hom[ f C.⋆ g ][ xᴰ , zᴰ ]} Cᴰ._⋆ᴰ_)
           where
    private
      import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
      module R = HomᴰReasoning Cᴰ

    redefine-id⋆ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    redefine-id⋆ .Categoryᴰ.ob[_] = Cᴰ.ob[_]
    redefine-id⋆ .Categoryᴰ.Hom[_][_,_] = Cᴰ.Hom[_][_,_]
    redefine-id⋆ .Categoryᴰ.isSetHomᴰ = Cᴰ.isSetHomᴰ
    redefine-id⋆ .Categoryᴰ.idᴰ = idᴰ' .fst
    redefine-id⋆ .Categoryᴰ._⋆ᴰ_ = ⋆ᴰ' .fst
    redefine-id⋆ .Categoryᴰ.⋆IdLᴰ {f = f}{xᴰ = xᴰ}{yᴰ = yᴰ} fᴰ = 
      subst (λ gᴰ → PathP (λ i → Cᴰ.Hom[ C .Category.⋆IdL f i ][ xᴰ , yᴰ ]) gᴰ fᴰ )
        -- todo: couldn't get congP₂ to work
        (R.≡[]-rectify λ i → ⋆ᴰ' .snd i (idᴰ' .snd i) fᴰ)
        (Cᴰ.⋆IdLᴰ fᴰ)
    redefine-id⋆ .Categoryᴰ.⋆IdRᴰ {f = f}{xᴰ}{yᴰ} fᴰ =
      subst (λ gᴰ → PathP (λ i → Cᴰ.Hom[ C .Category.⋆IdR f i ][ xᴰ , yᴰ ]) gᴰ fᴰ)
        (R.≡[]-rectify λ i → ⋆ᴰ' .snd i fᴰ (idᴰ' .snd i))
        (Cᴰ.⋆IdRᴰ fᴰ)
    redefine-id⋆ .Categoryᴰ.⋆Assocᴰ {x}{y}{z}{w}{f}{g}{h}{xᴰ}{yᴰ}{zᴰ}{wᴰ} fᴰ gᴰ hᴰ =
      subst2 (PathP (λ i → Cᴰ.Hom[ C .Category.⋆Assoc f g h i ][ xᴰ , wᴰ ]))
        (R.≡[]-rectify (λ i → ⋆ᴰ' .snd i (⋆ᴰ' .snd i fᴰ gᴰ) hᴰ))
        (R.≡[]-rectify (λ i → ⋆ᴰ' .snd i fᴰ (⋆ᴰ' .snd i gᴰ hᴰ)))
        (Cᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ)
