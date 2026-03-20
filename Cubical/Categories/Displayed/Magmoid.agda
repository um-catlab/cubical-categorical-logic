{-
  A Magmoidᴰ is a Categoryᴰ without the equations

  TODO: most of the stuff in this file doesn't actually have anything
  to do with Magmoids

-}
module Cubical.Categories.Displayed.Magmoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

-- Displayed categories with hom-sets
record Magmoidᴰ (C : Category ℓC ℓC') ℓCᴰ ℓCᴰ'
       : Type (ℓ-suc (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))) where
  no-eta-equality
  open Category C
  field
    ob[_] : ob → Type ℓCᴰ
    Hom[_][_,_] : {x y : ob} → Hom[ x , y ] → ob[ x ] → ob[ y ] → Type ℓCᴰ'
    idᴰ : ∀ {x} {p : ob[ x ]} → Hom[ id ][ p , p ]
    _⋆ᴰ_ : ∀ {x y z} {f : Hom[ x , y ]} {g : Hom[ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f ⋆ g ][ xᴰ , zᴰ ]

  infixr 9 _⋆ᴰ_
module _ {C : Category ℓC ℓC'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ

  -- TODO: this is an anti-pattern. This should all be passed as a big record rather than a ton of arguments
  module _ (idᴰ' : singl {A = ∀ {x} {p : Cᴰ.ob[ x ]} → Cᴰ.Hom[ C.id ][ p , p ]}
                         Cᴰ.idᴰ)
           (⋆ᴰ' : singl {A = ∀ {x y z} {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]}
             {xᴰ yᴰ zᴰ} → Cᴰ.Hom[ f ][ xᴰ , yᴰ ] → Cᴰ.Hom[ g ][ yᴰ , zᴰ ]
             → Cᴰ.Hom[ f C.⋆ g ][ xᴰ , zᴰ ]}
             Cᴰ._⋆ᴰ_)
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
      subst (λ gᴰ → PathP (λ i → Cᴰ.Hom[ C .Category.⋆IdL f i ][ xᴰ , yᴰ ])
        gᴰ fᴰ )
        -- todo: couldn't get congP₂ to work
        (R.rectify λ i → ⋆ᴰ' .snd i (idᴰ' .snd i) fᴰ)
        (Cᴰ.⋆IdLᴰ fᴰ)
    redefine-id⋆ .Categoryᴰ.⋆IdRᴰ {f = f}{xᴰ}{yᴰ} fᴰ =
      subst (λ gᴰ → PathP (λ i → Cᴰ.Hom[ C .Category.⋆IdR f i ][ xᴰ , yᴰ ])
        gᴰ fᴰ)
        (R.rectify λ i → ⋆ᴰ' .snd i fᴰ (idᴰ' .snd i))
        (Cᴰ.⋆IdRᴰ fᴰ)
    redefine-id⋆ .Categoryᴰ.⋆Assocᴰ {x}{y}{z}{w}{f}{g}{h}{xᴰ}{yᴰ}{zᴰ}{wᴰ}
      fᴰ gᴰ hᴰ =
      subst2 (PathP (λ i → Cᴰ.Hom[ C .Category.⋆Assoc f g h i ][ xᴰ , wᴰ ]))
        (R.rectify (λ i → ⋆ᴰ' .snd i (⋆ᴰ' .snd i fᴰ gᴰ) hᴰ))
        (R.rectify (λ i → ⋆ᴰ' .snd i fᴰ (⋆ᴰ' .snd i gᴰ hᴰ)))
        (Cᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ)

    private
      module RID = Categoryᴰ redefine-id⋆

    module _ {D : Category ℓD ℓD'}
             {F : Functor D C}
             (s : Section F Cᴰ)
             where
      open Section
      open Functor
      private
        module D = Category D

      redefine-id⋆S : Section F redefine-id⋆
      redefine-id⋆S .F-obᴰ = s .F-obᴰ
      redefine-id⋆S .F-homᴰ = s .F-homᴰ
      redefine-id⋆S .F-idᴰ =
        subst (λ idᴰ → (s .F-homᴰ D.id) RID.≡[ F .F-id ] idᴰ)
          (λ i → idᴰ' .snd i)
          (s .F-idᴰ)
      redefine-id⋆S .F-seqᴰ f g =
        subst (λ _⋆ᴰ_ →
              s .F-homᴰ (f D.⋆ g)
              RID.≡[ F .F-seq f g ]
              s .F-homᴰ f ⋆ᴰ s .F-homᴰ g)
          (λ i → ⋆ᴰ' .snd i)
          (s .F-seqᴰ f g)

    module _ {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
             {F : Functor D C}
             (Fᴰ : Functorᴰ F Dᴰ Cᴰ)
             where
      open Functorᴰ
      open Functor
      private
        module Dᴰ = Categoryᴰ Dᴰ
      redefine-id⋆F : Functorᴰ F Dᴰ redefine-id⋆
      redefine-id⋆F .F-obᴰ  = Fᴰ .F-obᴰ
      redefine-id⋆F .F-homᴰ = Fᴰ .F-homᴰ
      redefine-id⋆F .F-idᴰ {x}{xᴰ}  =
        subst (λ idᴰ → (Fᴰ .F-homᴰ (Dᴰ .Categoryᴰ.idᴰ)) RID.≡[ F .F-id ] idᴰ)
          (λ i → idᴰ' .snd i)
          (Fᴰ .F-idᴰ)
      redefine-id⋆F .F-seqᴰ {x} {y} {z} {f} {g} {xᴰ} {yᴰ} {zᴰ} fᴰ gᴰ =
        subst (λ _⋆ᴰ_ →
              Fᴰ .F-homᴰ (fᴰ Dᴰ.⋆ᴰ gᴰ)
              RID.≡[ F .F-seq f g ]
              Fᴰ .F-homᴰ fᴰ ⋆ᴰ Fᴰ .F-homᴰ gᴰ)
          (λ i → ⋆ᴰ' .snd i)
          (Fᴰ .F-seqᴰ fᴰ gᴰ)
