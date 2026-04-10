module Cubical.Categories.2Functor.Pseudofunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.2Category.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

private
  variable
    ℓC ℓC' ℓC'' ℓD ℓD' ℓD'' : Level

record Pseudofunctor (C : 2Category ℓC ℓC' ℓC'') (D : 2Category ℓD ℓD' ℓD'') :
    Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓC'') (ℓ-max (ℓ-max ℓD ℓD') ℓD'')) where
  no-eta-equality

  private
    module C = 2Category C
    module D = 2Category D

  field
    -- Action on objects
    F₀ : C.ob → D.ob

    -- Action on 1-morphisms
    F₁ : ∀ {x y : C.ob} → C.Hom₁[ x , y ] → D.Hom₁[ F₀ x , F₀ y ]

    -- Action on 2-cells
    F₂ : ∀ {x y : C.ob} {f g : C.Hom₁[ x , y ]}
       → C.Hom₂[ f , g ] → D.Hom₂[ F₁ f , F₁ g ]

    -- Preservation of identity 1-morphism
    F-id₁ : ∀ {x : C.ob} → F₁ (C.id₁ {x}) ≡ D.id₁ {F₀ x}

    -- Preservation of identity 2-cell
    F-id₂ : ∀ {x y : C.ob} {f : C.Hom₁[ x , y ]}
          → F₂ (C.id₂ {x} {y} {f}) ≡ D.id₂ {F₀ x} {F₀ y} {F₁ f}

    -- Preservation of horizontal composition (1-morphisms)
    F-seq₁ : ∀ {x y z : C.ob} (f : C.Hom₁[ x , y ]) (g : C.Hom₁[ y , z ])
           → F₁ (f C.⋆₁ g) ≡ (F₁ f) D.⋆₁ (F₁ g)

    -- Preservation of vertical composition (2-cells)
    F-seqⱽ : ∀ {x y : C.ob} {f g h : C.Hom₁[ x , y ]}
             (α : C.Hom₂[ f , g ]) (β : C.Hom₂[ g , h ])
           → F₂ (α C.⋆ⱽ β) ≡ (F₂ α) D.⋆ⱽ (F₂ β)

    -- Preservation of horizontal composition (2-cells)
    F-seqᴴ : ∀ {x y z : C.ob} {f f' : C.Hom₁[ x , y ]} {g g' : C.Hom₁[ y , z ]}
             (α : C.Hom₂[ f , f' ]) (β : C.Hom₂[ g , g' ])
           → PathP (λ i → D.Hom₂[ F-seq₁ f g i , F-seq₁ f' g' i ])
                   (F₂ (α C.⋆ᴴ β))
                   ((F₂ α) D.⋆ᴴ (F₂ β))

open Pseudofunctor
