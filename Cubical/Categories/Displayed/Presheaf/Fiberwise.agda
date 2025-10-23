{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Fiberwise where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)
open import Cubical.Categories.Displayed.Fibration.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Bifunctorᴰ
open Functorᴰ

open PshHom
open PshIso


-- A fiberwise presheaf is the definition of a presheaf that is
-- applicable to an indexed category C^op → Cat

-- i.e. if we have Cᴰ : C^op → Cat, then we want a section
-- Pⱽ : (x : C^op) → Psh Cᴰ.v[ x ] . This isn't right though.
--
-- (p : P[ x ]) → Psh Cᴰ.v[ x ]
-- (f : C [ y , x ]) → Psh Cᴰ.v[ x ] ⊸ Psh Cᴰ.v[ y ] over f*

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (isFib : isFibration Cᴰ)
  where
  private
    module P = PresheafNotation P
    module Cᴰ = Fibers Cᴰ
    module C = Category C
    module isFib {x}{y}(f : C [ y , x ])(xᴰ : Cᴰ.ob[ x ]) = UniversalElementⱽ (isFib xᴰ f)
  record Presheafᶠ (ℓPᴰ : Level)
    : Type (ℓ-max ℓPᴰ $ ℓ-max ℓCᴰ' $ ℓ-max ℓCᴰ $ ℓ-max ℓP $ ℓ-max ℓC' $ ℓ-max ℓC $ ℓ-suc ℓPᴰ) where
    constructor presheafᶠ
    field
      P-obᶠ  : ∀ {x} (p : P.p[ x ]) → Presheaf Cᴰ.v[ x ] ℓPᴰ

    p[_][_] : ∀ {x} → P.p[ x ] → Cᴰ.ob[ x ] → Type ℓPᴰ
    p[ p ][ xᴰ ] = ⟨ P-obᶠ p ⟅ xᴰ ⟆ ⟩

    _⋆ⱽᴰ_ : ∀ {x xᴰ yᴰ}{p : P.p[ x ]}(fⱽ : Cᴰ.v[ x ] [ xᴰ , yᴰ ])(pᴰ : p[ p ][ yᴰ ])
      → p[ p ][ xᴰ ]
    fⱽ ⋆ⱽᴰ pᴰ = (P-obᶠ _ ⟪ fⱽ ⟫) pᴰ

    _≡[_]_ : ∀ {x xᴰ} {f g : P.p[ x ]} → p[ f ][ xᴰ ] → f ≡ g → p[ g ][ xᴰ ]
      → Type ℓPᴰ
    _≡[_]_ {x} {xᴰ} {f} {g} fᴰ f≡g gᴰ = PathP (λ i → p[ f≡g i ][ xᴰ ]) fᴰ gᴰ

    _∫≡_ : ∀ {x xᴰ} {f g : P.p[ x ]}(fᴰ : p[ f ][ xᴰ ])(gᴰ : p[ g ][ xᴰ ])
      → Type _
    _∫≡_ {x}{xᴰ}{f}{g} fᴰ gᴰ = (f , fᴰ) ≡ (g , gᴰ)

    reind : ∀ {x}{xᴰ}{f g : P.p[ x ]}(f≡g : f ≡ g)
      → p[ f ][ xᴰ ] → p[ g ][ xᴰ ]
    reind = subst p[_][ _ ]

    field
      P-homᶠ : ∀ {x y} (f : C [ y , x ])(p : P.p[ x ])
        → PshHet (CartesianLiftF-fiber Cᴰ isFib f) (P-obᶠ p) (P-obᶠ (f P.⋆ p))

    _*_ : ∀ {x y}{xᴰ}{p : P.p[ x ]} (f : C [ y , x ])(pᴰ : p[ p ][ xᴰ ])
      → p[ f P.⋆ p ][ isFib.vertexⱽ f xᴰ ]
    f * pᴰ = P-homᶠ f _ .N-ob _ pᴰ
    field
      -- Just going to specify this manually for now, probably should
      -- make it some kind of natural trans equality or sthg
      P-idᶠ :  ∀ {x}{xᴰ} {p : P.p[ x ]} (pᴰ : p[ p ][ xᴰ ] )
        → (C.id * pᴰ)
            ∫≡
          (Cᴰ.reind (C.⋆IdL _) (isFib.elementⱽ C.id _) ⋆ⱽᴰ pᴰ)
      P-seqᶠ : ∀ {x y z xᴰ}{p : P.p[ x ]}(g : C [ z , y ])(f : C [ y , x ])(pᴰ : p[ p ][ xᴰ ])
        →
          ((g C.⋆ f) * pᴰ)
            ∫≡
          (isFib.introᴰ g _ (isFib.introᴰ f _ (Cᴰ.reind (sym $ C.⋆Assoc _ _ _) (isFib.elementⱽ (g C.⋆ f) xᴰ)))
            ⋆ⱽᴰ (g * (f * pᴰ)))

    opaque
      reind-filler : ∀ {x}{xᴰ}{f g : P.p[ x ]}(f≡g : f ≡ g)
        → (fᴰ : p[ f ][ xᴰ ])
        → fᴰ ∫≡ reind f≡g fᴰ
      reind-filler f≡g fᴰ = ΣPathP (f≡g , (subst-filler p[_][ _ ] f≡g fᴰ))

    _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p : P.p[ y ]}(fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ])(pᴰ : p[ p ][ yᴰ ])
      → p[ f P.⋆ p ][ xᴰ ]
    -- I can convert fᴰ to a Cᴰ.v[ x ][ xᴰ , f*yᴰ ]
    _⋆ᴰ_ {f = f} fᴰ pᴰ =
      isFib.introⱽ f _ (Cᴰ.reind (sym $ C.⋆IdL f) fᴰ) ⋆ⱽᴰ (f * pᴰ)


-- If Pⱽ is a presheafᴰ on Cᴰ over C [-][-, x ], then the following
-- things are all true:

-- 1. Pⱽ restricts to a presheaf on Cᴰ.v[ x ]. Call this Pⱽ.v the elements are just elements of Pⱽ over the identity on x

-- 2. For every f : C [ y , x ], Pⱽ can be restricted to a presheaf on Cᴰ.v[ y ]
--    (see `reindYo f Pⱽ`) Call this f*Pⱽ.v . The elements f*Pⱽ.v[ yᴰ ] can be defined as elements Pⱽ.p[ f ]
--

-- If Cᴰ is a fibration, then f induces a functor f* : Cᴰ.v[ x ] → Cᴰ.v[ y ]
-- 3. We get a presheaf heteromorphism f* : PshHet f* Pⱽ f*Pⱽ
--    this takes an element Pⱽ.p[ id {x} ][ xᴰ ] to an element Pⱽ.p[ f ][ f* xᴰ ]
-- 4.

