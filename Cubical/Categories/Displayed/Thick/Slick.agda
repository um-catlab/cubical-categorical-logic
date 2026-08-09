{-

  With a clever use of HITs, Thick displayed categories are just a special case of ordinary displayed categories.

-}
module Cubical.Categories.Displayed.Thick.Slick where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Level
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More hiding (_≡[_]_)

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.ExtraId
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Profunctor.Homomorphism.Bilinear
open import Cubical.Categories.Profunctor.Homomorphism.NaturalElement
open import Cubical.Categories.Profunctor.Homomorphism.Unary

open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCⱽ ℓCᴰ' ℓDᴰ ℓDⱽ ℓDᴰ' ℓP ℓP' ℓQ ℓQ' : Level

open Category
open NaturalElement

ThickCategoryᴰ : ∀ (C : Category ℓC ℓC') ℓCᴰ ℓCᴰ' → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓC) (ℓ-suc ℓC')) (ℓ-suc ℓCᴰ)) (ℓ-suc ℓCᴰ'))
ThickCategoryᴰ C ℓCᴰ ℓCᴰ' = Categoryᴰ (ExtraId C) ℓCᴰ ℓCᴰ'

module ThickCategoryᴰNotation {C : Category ℓC ℓC'} (Cᴰ : ThickCategoryᴰ C ℓCᴰ ℓCᴰ') where
  module Cᴰ = Fibers Cᴰ

  ob[_] : C .ob → Type _
  ob[_] = Cᴰ.ob[_]

  -- fiber category
  fiberCat : C .ob → Category ℓCᴰ ℓCᴰ'
  fiberCat x = Cᴰ.v[ x ]

  vHom[_,_] : ∀ {x} xᴰ xᴰ' → Type _
  vHom[_,_] {x} = fiberCat x .Hom[_,_]

  dHom[_][_,_] : ∀ {x y} (f : C [ x , y ]) xᴰ xᴰ' → Type _
  dHom[_][_,_] f = Cᴰ.Hom[ semHom f ][_,_]

  -- vertical composition
  _⋆ⱽ_ : ∀ {x}{xᴰ xᴰ' xᴰ'' : Cᴰ.ob[ x ]}
    → vHom[ xᴰ , xᴰ' ]
    → vHom[ xᴰ' , xᴰ'' ]
    → vHom[ xᴰ , xᴰ'' ]
  _⋆ⱽ_ = fiberCat _ ._⋆_

  private
    variable
      x y z : C .ob
      xᴰ xᴰ' xᴰ'' yᴰ yᴰ' yᴰ'' zᴰ : ob[ x ]
      f g h : C [ x , y ]
      fᴰ fᴰ' gᴰ gᴰ' hᴰ hᴰ' : dHom[ f ][ xᴰ , yᴰ ]
      fⱽ fⱽ' gⱽ gⱽ' hⱽ hⱽ' : vHom[ xᴰ , xᴰ' ]

  _⋆ᴰ_ = Cᴰ._⋆ᴰ_

  _⋆ⱽᴰ_ : vHom[ xᴰ , xᴰ' ] → dHom[ f ][ xᴰ' , yᴰ ]
    → dHom[ f ][ xᴰ , yᴰ ]
  _⋆ⱽᴰ_ = _⋆ᴰ_

  _⋆ᴰⱽ_ : dHom[ f ][ xᴰ , yᴰ ] → vHom[ yᴰ , yᴰ' ]
    → dHom[ f ][ xᴰ , yᴰ' ]
  _⋆ᴰⱽ_ = _⋆ᴰ_

  -- Normality in the strongest sense
  vtodPath : vHom[ xᴰ , xᴰ' ] ≡ dHom[ C .id ][ xᴰ , xᴰ' ]
  vtodPath {xᴰ = xᴰ} {xᴰ'} i = Cᴰ.Hom[ synId≡id Eq.refl i ][ xᴰ , xᴰ' ]

  vtod : vHom[ xᴰ , xᴰ' ] → dHom[ C .id ][ xᴰ , xᴰ' ]
  vtod {xᴰ = xᴰ} {xᴰ'} fⱽ = transport vtodPath fⱽ

  -- Every possible unit/associativity law you can think of is true
  -- Some examples:
  ⋆Assocⱽᴰᴰ :
    ∀ (fⱽ : vHom[ xᴰ , xᴰ' ]) (gᴰ : dHom[ g ][ xᴰ' , yᴰ ])(hᴰ : dHom[ h ][ yᴰ , zᴰ ])
    → (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰ hᴰ Cᴰ.≡[ (ExtraId C) .⋆Assoc (ExtraId C .id) (semHom g) (semHom h) ] fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰ hᴰ)
  ⋆Assocⱽᴰᴰ fⱽ gᴰ hᴰ = Cᴰ.⋆Assocᴰ fⱽ gᴰ hᴰ

  ⋆ⱽᴰ≡⋆ᴰ :
    ∀ (fⱽ : vHom[ xᴰ , xᴰ' ]) (gᴰ : dHom[ g ][ xᴰ' , yᴰ ])
    → fⱽ ⋆ⱽᴰ gᴰ Cᴰ.≡[ cong semHom (sym (⋆IdL C g)) ] vtod fⱽ ⋆ᴰ gᴰ
  ⋆ⱽᴰ≡⋆ᴰ fⱽ gᴰ = Cᴰ.rectifyOut (Cᴰ.⟨ Cᴰ.reind-revealed-filler _ ⟩⋆⟨⟩)

  ⋆IdRᴰⱽ : ∀ (fᴰ : dHom[ f ][ xᴰ , yᴰ ]) (gⱽ : vHom[ yᴰ , yᴰ' ])
    → fᴰ ⋆ᴰⱽ gⱽ Cᴰ.≡[ cong semHom $ sym $ ⋆IdR C f ] fᴰ ⋆ᴰ vtod gⱽ
  ⋆IdRᴰⱽ fᴰ gⱽ = Cᴰ.rectifyOut Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-revealed-filler _ ⟩
