module Cubical.Categories.2Functor.Lax where

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
    ℓ ℓ' ℓ'' ℓC ℓC' ℓC'' ℓD ℓD' ℓD'' : Level

record LaxFunctor (C : 2Category ℓC ℓC' ℓC'') (D : 2Category ℓD ℓD' ℓD'') :
    Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓC'') (ℓ-max (ℓ-max ℓD ℓD') ℓD''))
    where
  no-eta-equality

  private
    module C = 2Category C
    module D = 2Category D

  field
    F₀ : C.ob → D.ob
    F₁ : ∀ {x y} → C.Hom₁[ x , y ] → D.Hom₁[ F₀ x , F₀ y ]
    F₂ : ∀ {x y} {f g : C.Hom₁[ x , y ]}
       → C.Hom₂[ f , g ] → D.Hom₂[ F₁ f , F₁ g ]

    F-id : ∀ {x} → D.Hom₂[ D.id₁ , F₁ (C.id₁ {x}) ]

    F-seq : ∀ {x y z} (f : C.Hom₁[ x , y ]) (g : C.Hom₁[ y , z ])
          → D.Hom₂[ (F₁ f) D.⋆₁ (F₁ g) , F₁ (f C.⋆₁ g) ]

    F-id₂ : ∀ {x y} {f : C.Hom₁[ x , y ]}
          → F₂ (C.id₂ {f = f}) ≡ D.id₂ {f = F₁ f}

    F-seqⱽ : ∀ {x y} {f g h : C.Hom₁[ x , y ]}
             (α : C.Hom₂[ f , g ]) (β : C.Hom₂[ g , h ])
           → F₂ (α C.⋆ⱽ β) ≡ (F₂ α) D.⋆ⱽ (F₂ β)

    F-seqᴴ : ∀ {x y z} {f f' : C.Hom₁[ x , y ]} {g g' : C.Hom₁[ y , z ]}
             (α : C.Hom₂[ f , f' ]) (β : C.Hom₂[ g , g' ])
           → (F-seq f g) D.⋆ⱽ F₂ (α C.⋆ᴴ β)
             ≡ ((F₂ α) D.⋆ᴴ (F₂ β)) D.⋆ⱽ (F-seq f' g')

    F-unitality-l : ∀ {x y} (f : C.Hom₁[ x , y ])
                  → PathP (λ i → D.Hom₂[ D.⋆₁IdL (F₁ f) i , F₁ (C.⋆₁IdL f i) ])
                          ((F-id D.⋆ᴴ D.id₂) D.⋆ⱽ (F-seq C.id₁ f))
                          (F₂ C.id₂)

    F-unitality-r : ∀ {x y} (f : C.Hom₁[ x , y ])
                  → PathP (λ i → D.Hom₂[ D.⋆₁IdR (F₁ f) i , F₁ (C.⋆₁IdR f i) ])
                          ((D.id₂ D.⋆ᴴ F-id) D.⋆ⱽ (F-seq f C.id₁))
                          (F₂ C.id₂)

    F-associativity : ∀ {w x y z} (f : C.Hom₁[ w , x ])
                        (g : C.Hom₁[ x , y ]) (h : C.Hom₁[ y , z ])
                    → PathP (λ i → D.Hom₂[ D.⋆₁Assoc (F₁ f) (F₁ g) (F₁ h) i
                                         , F₁ (C.⋆₁Assoc f g h i) ])
                            ((F-seq f g D.⋆ᴴ D.id₂) D.⋆ⱽ F-seq (f C.⋆₁ g) h)
                            ((D.id₂ D.⋆ᴴ (F-seq g h)) D.⋆ⱽ F-seq f (g C.⋆₁ h))

open 2Category
module _ (C : 2Category ℓ ℓ' ℓ'') where
  private module C = 2Category C
  record isIso2Cell {x y : C.ob}
    {f g : C.Hom₁[ x , y ]} (α : C.Hom₂[ f , g ]) : Type ℓ'' where
    field
      inv : C.Hom₂[ g , f ]
      sec : α C.⋆ⱽ inv ≡ C.id₂
      ret : inv C.⋆ⱽ α ≡ C.id₂

record isPseudo {C : 2Category ℓC ℓC' ℓC''} {D : 2Category ℓD ℓD' ℓD''}
                (F : LaxFunctor C D) :
    Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓC'') (ℓ-max (ℓ-max ℓD ℓD') ℓD'')) where
  private
    module F = LaxFunctor F
    module C = 2Category C
    module D = 2Category D
  field
    F-id-iso : ∀ {x} → isIso2Cell D (F.F-id {x})
    F-seq-iso : ∀ {x y z} (f : C.Hom₁[ x , y ]) (g : C.Hom₁[ y , z ])
              → isIso2Cell D (F.F-seq f g)

record PseudoFunctor (C : 2Category ℓC ℓC' ℓC'') (D : 2Category ℓD ℓD' ℓD'') :
    Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓC'') (ℓ-max (ℓ-max ℓD ℓD') ℓD'')) where
  field
    lax : LaxFunctor C D
    pseudo : isPseudo lax
  open LaxFunctor lax public
