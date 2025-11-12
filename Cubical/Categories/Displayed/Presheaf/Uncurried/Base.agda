{-

  Our main definition of a displayed presheaf Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ
  is a displayed functor over the presheaf P:

  Pᴰ : Cᴰ ^opᴰ → Setᴰ ℓPᴰ
  |    |          |
  P  : C  ^op → Set ℓP

  This formulation makes defining "displayed" constructions very easy, e.g., see the displayed exponential, which can be modeled directly on the exponential of Presheaves.

  However, certain constructions on displayed presheaves are quite awkward when formulated this way, especially the *vertical* exponentials and the universal quantifier.

  The difficulty is that the output displayed presheaf depends on not just objects x : C and xᴰ : Cᴰ.ob[ x ], but also on an element p : P.p[ x ]. Constructions like the vertical exponential use the element p in a non-trivial way by reindexing a presheaf. But there doesn't seem to be any way to directly express that reindexing as itself some kind of functor in a way we can use with this formulation, because the dependency on p is part of the definition of Setᴰ.

  What we need is an "uncurried" definition of a displayed presheaf, where the p : P.p[ x ] part is expressed in the domain of an ordinary presheaf:

    Pᴰ : (x : C , xᴰ : Cᴰ.ob[ x ], p : P.p[ x ])^op → Set ℓPᴰ

  The category in the domain here can be defined using compositional constructions: the category of elements of P displayed over C, vertical product of displayed categories and total categories.

  Then we can define an isomorphism between our original "curried" definition and this "uncurried" one.
  Further, this extends to an isomorphism of categories: natural transformations between uncurried displayed presheaves correspond to *vertical* natural transformations between curried displayed presheaves. This means that all *vertical* universal properties can be expressed in terms of either curried or uncurried displayed presheaves.

-}

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Functor
open Functorᴰ
open PshIso

-- TODO: better name...
-- I guess there isn't really anything very slice-like about this...
_/_ : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (P : Presheaf C ℓP) → Category _ _
Cᴰ / P = ∫C (Cᴰ ×ᴰ Element P)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  {F : Functor C D}
  where
  _/Fᴰ_ : (Fᴰ : Functorᴰ F Cᴰ Dᴰ) → (α : PshHet F P Q) → Functor (Cᴰ / P) (Dᴰ / Q)
  Fᴰ /Fᴰ α = ∫F {F = F} (Fᴰ ×ᴰF PshHet→ElementFunctorᴰ α)

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  where
  _/Fⱽ_ : (Fᴰ : Functorⱽ Cᴰ Dᴰ) → (α : PshHom P Q) → Functor (Cᴰ / P) (Dᴰ / Q)
  Fᴰ /Fⱽ α = Fᴰ /Fᴰ (α ⋆PshHom reindPshId≅ Q .trans)

-- Interestingly, this one is at a lower universe level than Curried.Presheafᴰ
-- Use modules to distinguish this from Curried.Presheafᴰ
Presheafᴰ : {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
           → (ℓPᴰ : Level)
           → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓCᴰ) ℓCᴰ') (ℓ-suc ℓPᴰ))
Presheafᴰ {ℓP = ℓP} P Cᴰ ℓPᴰ = Presheaf (Cᴰ / P) ℓPᴰ

PresheafᴰCategory : {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') → (ℓPᴰ : Level)
  → Category _ _
PresheafᴰCategory P Cᴰ ℓPᴰ = PresheafCategory (Cᴰ / P) ℓPᴰ

Presheafⱽ : {C : Category ℓC ℓC'} (x : C .ob)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
           → (ℓPᴰ : Level)
           → Type _
Presheafⱽ {C = C} x = Presheafᴰ (C [-, x ])

module PresheafᴰNotation {C : Category ℓC ℓC'}
  -- Cᴰ and P *must* be supplied, Cᴰ for type-checking and P for performance.
  -- revisit this once no-eta-equality for categories is turned on
  (Cᴰ : Categoryᴰ C ℓD ℓD')
  (P : Presheaf C ℓP)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
  infixr 9 _⋆ᴰ_

  p[_][_] : ∀ {x} → P.p[ x ] → Cᴰ.ob[ x ] → Type ℓPᴰ
  p[ p ][ xᴰ ] = ⟨ Pᴰ .F-ob (_ , xᴰ , p) ⟩

  isSetPshᴰ : ∀ {x}{p : P.p[ x ]}{xᴰ} → isSet p[ p ][ xᴰ ]
  isSetPshᴰ = Pᴰ .F-ob _ .snd

  module pReasoning {x}{xᴰ : Cᴰ.ob[ x ]} = hSetReasoning (P .F-ob x) p[_][ xᴰ ]
  open pReasoning renaming (_P≡[_]_ to _≡[_]_; Prectify to rectify) public

  _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p} (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (pᴰ : p[ p ][ yᴰ ])
    → p[ f P.⋆ p ][ xᴰ ]
  fᴰ ⋆ᴰ pᴰ = Pᴰ .F-hom (_ , fᴰ , refl) pᴰ

  opaque
    ⋆ᴰ-reind : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p q}(fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (f⋆p≡q : f P.⋆ p ≡ q) (pᴰ : p[ p ][ yᴰ ])
      → Pᴰ .F-hom (f , fᴰ , f⋆p≡q) pᴰ ≡ reind f⋆p≡q (fᴰ ⋆ᴰ pᴰ)
    ⋆ᴰ-reind {x}{y}{xᴰ}{yᴰ} {f = f}{p}{q} fᴰ f⋆p≡q pᴰ = rectify $ ≡out $ (sym $ ≡in $ lem) ∙ reind-filler f⋆p≡q where
      lem : PathP (λ i → ⟨ Pᴰ .F-ob (x , xᴰ , f⋆p≡q i ) ⟩)
        (Pᴰ .F-hom (f , fᴰ , (λ _ → P .F-hom f p)) pᴰ)
        (Pᴰ .F-hom (f , fᴰ , f⋆p≡q) pᴰ)
      lem i = Pᴰ .F-hom (f , fᴰ , λ j → f⋆p≡q (i ∧ j)) pᴰ

    ⋆IdLᴰ : ∀ {x}{xᴰ}{p : P.p[ x ]}(pᴰ : p[ p ][ xᴰ ])
      → (Pᴰ .F-hom (C.id , Cᴰ.idᴰ , refl {x = C.id P.⋆ p}) pᴰ) ∫≡ pᴰ
    ⋆IdLᴰ {x}{xᴰ}{p} pᴰ = reind-filler _ ∙ (≡in $ (sym $ ⋆ᴰ-reind _ _ _) ∙ funExt⁻ (Pᴰ .F-id) pᴰ)

    ⋆Assocᴰ : ∀ {x y z}{xᴰ yᴰ zᴰ}{f : C [ z , y ]}{g : C [ y , x ]}{p : P.p[ x ]}
      (fᴰ : Cᴰ [ f ][ zᴰ , yᴰ ])
      (gᴰ : Cᴰ [ g ][ yᴰ , xᴰ ])
      (pᴰ : p[ p ][ xᴰ ])
      → ((fᴰ Cᴰ.⋆ᴰ gᴰ) ⋆ᴰ pᴰ) ∫≡ (fᴰ ⋆ᴰ gᴰ ⋆ᴰ pᴰ)
    ⋆Assocᴰ {x} {y} {z} {xᴰ} {yᴰ} {zᴰ} {f} {g} {p} fᴰ gᴰ pᴰ =
      reind-filler _
      ∙ (≡in $ (sym $ ⋆ᴰ-reind _ _ _) ∙ funExt⁻ (Pᴰ .F-seq (g , gᴰ , refl) (f , fᴰ , refl)) _)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
  PshHomⱽ : Type _
  PshHomⱽ = PshHom Pᴰ Qᴰ

  PshIsoⱽ : Type _
  PshIsoⱽ = PshIso Pᴰ Qᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
  isPshIsoⱽ : PshHomⱽ Pᴰ Qᴰ → Type _
  isPshIsoⱽ = isPshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  where
  idPshIsoⱽ : PshIsoⱽ Pᴰ Pᴰ
  idPshIsoⱽ = idPshIso

  idPshHomⱽ : PshHomⱽ Pᴰ Pᴰ
  idPshHomⱽ = idPshHom

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
  where
  invPshIsoⱽ : PshIsoⱽ Pᴰ Qᴰ → PshIsoⱽ Qᴰ Pᴰ
  invPshIsoⱽ = invPshIso

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
  where
  _⋆PshHomⱽ_ : (αᴰ : PshHomⱽ Pᴰ Qᴰ)(βᴰ : PshHomⱽ Qᴰ Rᴰ) → PshHomⱽ Pᴰ Rᴰ
  _⋆PshHomⱽ_ = _⋆PshHom_

  _⋆PshIsoⱽ_ : (αᴰ : PshIsoⱽ Pᴰ Qᴰ)(βᴰ : PshIsoⱽ Qᴰ Rᴰ) → PshIsoⱽ Pᴰ Rᴰ
  _⋆PshIsoⱽ_ = _⋆PshIso_

  infixr 9 _⋆PshHomⱽ_
  infixr 9 _⋆PshIsoⱽ_
