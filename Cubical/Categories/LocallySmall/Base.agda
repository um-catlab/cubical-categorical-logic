-- TODO: some stuff in this file should probably be moved around.

-- The notion of Category ℓC ℓC' in Cubical.Categories.Category is
-- analogous to the set theoretic notion of a *small* category: the
-- types of the category are ℓC-small and the hom sets are all
-- ℓC'-small.
--
-- This is too restrictive to model many constructions in type
-- theory. The most paradigmatic example is the Category of hSets SET.
-- For SET to be a small category, we must fix the universe level SET
-- ℓ.  But this is overly restrictive, as the notion of function f : A → B
-- in type theory doesn't dictate that A and B have the same universe
-- level. This limits the utility of the category theory library.

-- As an example, the product of sets A × B has the universal property
-- of being a categorical product. If this is stated in terms of fixed
-- universe levels, we get an overly specific theorem: given A B C :
-- hSet ℓ, that functions C → A × B are in natural isomorphism with
-- pairs of functions (C → A) × (C → B). But this same theorem holds
-- when all of A, B and C are allowed to have different universe
-- levels, and idiomatic Agda code should be as universe-polymorphic
-- as possible, lest users of the code are forced to insert tedious
-- Lift operations everywhere in order to use them.
--
-- We can solve this issue by embracing two generalizations of small categories:

-- - Locally Small categories, whose type of objects is "large", i.e.,
--   in Typeω, whereas every hom set has a universe level (that can
--   depend on the objects)

-- - *Displayed* Categories, which allow us to talk about morphisms
--   between objects that are of a different "type". E.g., we can
--   define a category of sets *displayed over* the set of universe
--   levels. The objects are of a provided universe level and the
--   morphisms are merely all functions!

-- The connection between these two is that a Displayed Locally Small
-- Category has a locally small total category. For example, the total
-- category of the category of sets displayed over universe levels is
-- the Locally small category of "All small Sets" whose objects are
-- pairs of a universe level ℓ and an hSet ℓ and morphisms are
-- functions. This allows us to then form the displayed category of
-- all indexed sets, displyaed over the indexing set and the universe
-- level of the indexed sets.

module Cubical.Categories.LocallySmall.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Prod using (_×ω_; _,_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
-- open import Cubical.Categories.Displayed.Base using (Categoryᴰ)

private
  variable
    ℓ ℓ' ℓ1 ℓ2 ℓw ℓx ℓy ℓz ℓC ℓC' : Level
    ℓᴰ ℓᴰ' ℓ1ᴰ ℓ2ᴰ ℓwᴰ ℓxᴰ ℓyᴰ ℓzᴰ ℓCᴰ ℓCᴰ' : Level
    Cob Dob Eob : Typeω
    C-ℓ : Cob → Cob → Level
    D-ℓ : Dob → Dob → Level
    E-ℓ : Eob → Eob → Level
    Cobᴰ : Cob → Typeω
    Cobᴰ-ℓ : Cob → Level
    Dobᴰ : Dob → Typeω
    CHom-ℓᴰ : ∀ (x y : Cob)(xᴰ : Cobᴰ x)(yᴰ : Cobᴰ y) → Level

open _×ω_

record Σω (A : Typeω) (B : A → Typeω) : Typeω where
  constructor _,_
  field
    fst : A
    snd : B fst

Σω-syntax : ∀ (A : Typeω) (B : A → Typeω) → Typeω
Σω-syntax = Σω

syntax Σω-syntax A (λ x → B) = Σω[ x ∈ A ] B

open Σω

record Liftω (A : Type ℓ) : Typeω where
  constructor liftω
  field
    lowerω : A

open Liftω

mapω : {A : Type ℓ}{B : Type ℓ'} → (A → B) → Liftω A → Liftω B
mapω f a = liftω (f (a .lowerω))

mapω' : {A : Type ℓ}{β : A → Level} (f : (a : A) → Type (β a)) (a : Liftω A) → Typeω
mapω' f a = Liftω (f (a .lowerω))

-- TODO: rename to just "Category"
-- A LocallySmallCategory has a "proper class" of objects, but small hom sets

-- We prefer this as the primitive over Large categories because we
-- can't use the ≡ type for Large categories.

-- we make Hom-ℓ a parameter because it makes it possible to abstract
-- over stronger "smallness" conditions
record Category (ob : Typeω) (Hom-ℓ : ob → ob → Level) : Typeω where
  no-eta-equality
  field
    Hom[_,_] : ∀ x y → Type (Hom-ℓ x y)
    id : ∀ {x} → Hom[ x , x ]
    _⋆_ : ∀ {x y z}(f : Hom[ x , y ])(g : Hom[ y , z ]) → Hom[ x , z ]
    ⋆IdL : ∀ {x y}(f : Hom[ x , y ]) → id ⋆ f ≡ f
    ⋆IdR : ∀ {x y}(f : Hom[ x , y ]) → f ⋆ id ≡ f
    ⋆Assoc  : ∀ {w x y z}(f : Hom[ w , x ])(g : Hom[ x , y ])(h : Hom[ y , z ])
      → ((f ⋆ g) ⋆ h) ≡ (f ⋆ (g ⋆ h))
    isSetHom : ∀ {x y} → isSet Hom[ x , y ]
  infixr 9 _⋆_

  ⟨_⟩⋆⟨_⟩ : {x y z : ob} {f f' : Hom[ x , y ]} {g g' : Hom[ y , z ]}
          → f ≡ f' → g ≡ g' → f ⋆ g ≡ f' ⋆ g'
  ⟨ ≡f ⟩⋆⟨ ≡g ⟩ = cong₂ _⋆_ ≡f ≡g

  ⟨⟩⋆⟨_⟩ : ∀ {x y z} {f : Hom[ x , y ]} {g g' : Hom[ y , z ]}
          → g ≡ g' → f ⋆ g ≡ f ⋆ g'
  ⟨⟩⋆⟨ ≡g ⟩ = cong (_ ⋆_) ≡g

  ⟨_⟩⋆⟨⟩ : ∀ {x y z} {f f' : Hom[ x , y ]} {g : Hom[ y , z ]}
          → f ≡ f' → f ⋆ g ≡ f' ⋆ g
  ⟨ ≡f ⟩⋆⟨⟩ = cong (_⋆ _) ≡f

open Category

-- A (LS) Category with a small type of objects
SmallObjectsCategory : ∀ {ℓC}(ob : Type ℓC)(C-ℓ : ob → ob → Level) → Typeω
SmallObjectsCategory ob C-ℓ = Category (Liftω ob) λ (liftω x) (liftω y) → C-ℓ x y

-- A (LS) Category such that all hom sets are at the *same* universe level
GloballySmallCategory : (Cob : Typeω)(ℓC' : Level) → Typeω
GloballySmallCategory Cob ℓC' = Category Cob λ _ _ → ℓC'

-- A category is small if it both has small objects and is globally
-- small.
-- This is the only variant that is itself a small type: the
-- definition of Category in Cubical.Categories.Category
SmallCategory : ∀ ℓC (ℓC' : Level) → Typeω
SmallCategory ℓC ℓC' = Σω[ (liftω ob) ∈ Liftω (Type ℓC) ] GloballySmallCategory (Liftω ob) ℓC'

module _ (C : Small.Category ℓC ℓC') where
  private
    module C = Small.Category C
  |mkSmallCategory| : GloballySmallCategory (Liftω C.ob) ℓC'
  |mkSmallCategory| .Hom[_,_] (liftω x) (liftω y) = C.Hom[ x , y ]
  |mkSmallCategory| .id = C.id
  |mkSmallCategory| ._⋆_ = C._⋆_
  |mkSmallCategory| .⋆IdL = C.⋆IdL
  |mkSmallCategory| .⋆IdR = C.⋆IdR
  |mkSmallCategory| .⋆Assoc = C.⋆Assoc
  |mkSmallCategory| .isSetHom = C.isSetHom

  mkSmallCategory : SmallCategory ℓC ℓC'
  mkSmallCategory = liftω C.ob , |mkSmallCategory|

module _ ((Cob , C) : SmallCategory ℓC ℓC') where
  open Small.Category
  private
    module C = Category C
  SmallLocallySmallCategory→SmallCategory : Small.Category ℓC ℓC'
  SmallLocallySmallCategory→SmallCategory .ob = Cob .lowerω
  SmallLocallySmallCategory→SmallCategory .Hom[_,_] x y = C.Hom[ liftω x , liftω y ]
  SmallLocallySmallCategory→SmallCategory .id = C.id
  SmallLocallySmallCategory→SmallCategory ._⋆_ = C._⋆_
  SmallLocallySmallCategory→SmallCategory .⋆IdL = C.⋆IdL
  SmallLocallySmallCategory→SmallCategory .⋆IdR = C.⋆IdR
  SmallLocallySmallCategory→SmallCategory .⋆Assoc = C.⋆Assoc
  SmallLocallySmallCategory→SmallCategory .isSetHom = C.isSetHom

module _ (C : Category Cob C-ℓ) where
  private
    module C = Category C

  record CatIso (x y : Cob) : Type (ℓ-max (C-ℓ x x) $ ℓ-max (C-ℓ y y) $ ℓ-max (C-ℓ y x) (C-ℓ x y)) where
    no-eta-equality
    constructor iso
    field
      fun : C.Hom[ x , y ]
      inv : C.Hom[ y , x ]
      sec : inv C.⋆ fun ≡ C.id
      ret : fun C.⋆ inv ≡ C.id

  isIso : ∀ {x y}(f : C.Hom[ x , y ]) → Type _
  isIso {x}{y} f = (Σ[ inv ∈ C.Hom[ y , x ] ] ((inv C.⋆ f ≡ C.id) × (f C.⋆ inv ≡ C.id)))

  CatIsoIsoΣ : ∀ {x y}
    → Iso (CatIso x y)
          (Σ[ fun ∈ C.Hom[ x , y ] ] isIso fun)
  unquoteDef CatIsoIsoΣ = defineRecordIsoΣ CatIsoIsoΣ (quote (CatIso))

  isPropIsIso : ∀ {x y}{f : C.Hom[ x , y ]} → isProp (isIso f)
  isPropIsIso {f = f} inv inv' = Σ≡Prop (λ _ → isProp× (C.isSetHom _ _) (C.isSetHom _ _))
    (sym (C.⋆IdR _)
    ∙ C.⟨⟩⋆⟨ sym $ inv' .snd .snd ⟩
    ∙ sym (C.⋆Assoc _ _ _)
    ∙ C.⟨ inv .snd .fst ⟩⋆⟨⟩
    ∙ C.⋆IdL (inv' .fst))

  idCatIso : ∀ {x} → CatIso x x
  idCatIso = iso C.id C.id (C.⋆IdL C.id) (C.⋆IdL C.id)

  ⋆CatIso : ∀ {x y z} → CatIso x y → CatIso y z → CatIso x z
  ⋆CatIso f g = iso
    (f .CatIso.fun C.⋆ g .CatIso.fun)
    (g .CatIso.inv C.⋆ f .CatIso.inv)
    (C.⋆Assoc _ _ _ ∙ C.⟨⟩⋆⟨ sym (C.⋆Assoc _ _ _) ∙ C.⟨ f .CatIso.sec ⟩⋆⟨⟩ ∙ C.⋆IdL (g .CatIso.fun) ⟩ ∙ g .CatIso.sec)
    (C.⋆Assoc _ _ _ ∙ C.⟨⟩⋆⟨ sym (C.⋆Assoc _ _ _) ∙ C.⟨ g .CatIso.ret ⟩⋆⟨⟩ ∙ C.⋆IdL (f .CatIso.inv) ⟩ ∙ f .CatIso.ret)

  CatIso≡ : ∀ {x y} {f g : CatIso x y}
    → f .CatIso.fun ≡ g .CatIso.fun
    → f ≡ g
  CatIso≡ f≡g = isoFunInjective CatIsoIsoΣ _ _ (Σ≡Prop (λ _ → isPropIsIso) f≡g)

  ISO : Category Cob _
  ISO .Hom[_,_] = CatIso
  ISO .id = idCatIso
  ISO ._⋆_ = ⋆CatIso
  ISO .⋆IdL = λ _ → CatIso≡ (C.⋆IdL _)
  ISO .⋆IdR = λ _ → CatIso≡ (C.⋆IdR _)
  ISO .⋆Assoc _ _ _ = CatIso≡ (C.⋆Assoc _ _ _)
  ISO .isSetHom = isSetIso CatIsoIsoΣ (isSetΣ C.isSetHom (λ _ → isProp→isSet isPropIsIso))

  module CategoryNotation where
    open Category C public
    ISOC = ISO
    module ISOC = Category ISOC
    ISOC≡ : ∀ {x y} {f g : ISOC.Hom[ x , y ]}
      → f .CatIso.fun ≡ g .CatIso.fun
      → f ≡ g
    ISOC≡ = CatIso≡

    invCatIso : ∀ {x y} (f : ISOC.Hom[ x , y ]) → ISOC.Hom[ y , x ]
    invCatIso f .CatIso.fun = f .CatIso.inv
    invCatIso f .CatIso.inv = f .CatIso.fun
    invCatIso f .CatIso.sec = f .CatIso.ret
    invCatIso f .CatIso.ret = f .CatIso.sec

    -- The following two lemmas are just that the Yoneda embedding is a
    -- functor and therefore preserves iso
    ⋆CatIso-Iso : ∀ {x y} → CatIso x y → ∀ {z} → Iso C.Hom[ z , x ] C.Hom[ z , y ]
    ⋆CatIso-Iso f = iso (C._⋆ f .CatIso.fun) (C._⋆ f .CatIso.inv)
      (λ g → C.⋆Assoc _ _ _ ∙ C.⟨⟩⋆⟨ f .CatIso.sec ⟩ ∙ C.⋆IdR g)
      (λ g → C.⋆Assoc _ _ _ ∙ C.⟨⟩⋆⟨ f .CatIso.ret ⟩ ∙ C.⋆IdR g)

    CatIso⋆-Iso : ∀ {x y} → CatIso x y → ∀ {z} → Iso C.Hom[ y , z ] C.Hom[ x , z ]
    CatIso⋆-Iso f = iso (f .CatIso.fun C.⋆_) (f .CatIso.inv C.⋆_)
      (λ g → sym (C.⋆Assoc _ _ _) ∙ C.⟨ f .CatIso.ret ⟩⋆⟨⟩ ∙ C.⋆IdL g)
      (λ g → sym (C.⋆Assoc _ _ _) ∙ C.⟨ f .CatIso.sec ⟩⋆⟨⟩ ∙ C.⋆IdL g)

    subst-CatIso : ∀ {x y g g⁻}
      (f : CatIso x y)
      (f≡g : f .CatIso.fun ≡ g)
      (f⁻≡g⁻ : f .CatIso.inv ≡ g⁻)
      → CatIso x y
    subst-CatIso {x}{y}{g}{g⁻} f f≡g f⁻≡g⁻ = iso g g⁻
      (subst {A = C.Hom[ x , y ] × C.Hom[ y , x ]} (λ (g , g⁻) → g⁻ C.⋆ g ≡ C.id) (ΣPathP (f≡g , f⁻≡g⁻)) (f .CatIso.sec))
      (subst {A = C.Hom[ x , y ] × C.Hom[ y , x ]} (λ (g , g⁻) → g C.⋆ g⁻ ≡ C.id) (ΣPathP (f≡g , f⁻≡g⁻)) (f .CatIso.ret))

-- -- The key thing we need is to be able to iterate the ∫C construction
-- module _ (C : Category Cob C-ℓ) where
--   private
--     module C = Category C
--   -- Hom-ℓᴰ can't depend on f without making _≡[_]_ ill typed
--   record Categoryᴰ (ob[_] : Cob → Typeω)(Hom-ℓᴰ : ∀ x y (xᴰ : ob[ x ])(yᴰ : ob[ y ]) → Level)
--     : Typeω where
--     no-eta-equality
--     field
--       Hom[_][_,_] : ∀ {x y}(f : C.Hom[ x , y ])(xᴰ : ob[ x ])(yᴰ : ob[ y ])
--         → Type (Hom-ℓᴰ _ _ xᴰ yᴰ)
--       idᴰ : ∀ {x} {xᴰ : ob[ x ]} → Hom[ C.id ][ xᴰ , xᴰ ]
--       _⋆ᴰ_ : ∀ {x y z} {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]} {xᴰ yᴰ zᴰ}
--         → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f C.⋆ g ][ xᴰ , zᴰ ]
--     infixr 9 _⋆ᴰ_

--     _≡[_]_ : ∀ {x y xᴰ yᴰ} {f g : C.Hom[ x , y ]}
--       → (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (p : f ≡ g) (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
--       → Type (Hom-ℓᴰ _ _ xᴰ yᴰ)
--     _≡[_]_ {x} {y} {xᴰ} {yᴰ} fᴰ p gᴰ = PathP (λ i → Hom[ p i ][ xᴰ , yᴰ ]) fᴰ gᴰ

--     infix 2 _≡[_]_

--     ∫Hom[_,_] : (x y : Σω Cob ob[_]) → Type _
--     ∫Hom[ xxᴰ , yyᴰ ] =
--       Σ[ f ∈ C.Hom[ xxᴰ .fst , yyᴰ .fst ] ]
--       Hom[ f ][ xxᴰ .snd , yyᴰ .snd ]

--     _∫≡_ :  ∀ {x y xᴰ yᴰ} {f g : C.Hom[ x , y ]}
--       → (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
--       → Type _
--     fᴰ ∫≡ gᴰ = Path ∫Hom[ _ , _ ] (_ , fᴰ) (_ , gᴰ)
--     infix 2 _∫≡_

--     field
--       ⋆IdLᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
--         → idᴰ ⋆ᴰ fᴰ ∫≡ fᴰ
--       ⋆IdRᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
--         → fᴰ ⋆ᴰ idᴰ ∫≡ fᴰ
--       ⋆Assocᴰ : ∀ {x y z w} {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]}  {h : C.Hom[ z , w ]} {xᴰ yᴰ zᴰ wᴰ}
--         (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ yᴰ , zᴰ ]) (hᴰ : Hom[ h ][ zᴰ , wᴰ ])
--         → (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ ∫≡ fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ)
--       isSetHomᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} → isSet Hom[ f ][ xᴰ , yᴰ ]

--     -- Reindexing displayed morphisms along an equality in the base
--     reind : {x y : Cob}{f g : C.Hom[ x , y ]}
--       {xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
--       (p : f ≡ g)
--       (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
--       → Hom[ g ][ xᴰ , yᴰ ]
--     reind = subst Hom[_][ _ , _ ]

--     _⋆ⱽᴰ_ : ∀ {x y} {xᴰ xᴰ' yᴰ}{g : C.Hom[ x , y ]}
--       (fⱽ : Hom[ C.id ][ xᴰ , xᴰ' ])
--       (gᴰ : Hom[ g ][ xᴰ' , yᴰ ])
--       → Hom[ g ][ xᴰ , yᴰ ]
--     fⱽ ⋆ⱽᴰ gᴰ = reind (C.⋆IdL _) (fⱽ ⋆ᴰ gᴰ)

--     _⋆ⱽ_ : ∀ {x} {xᴰ xᴰ' xᴰ''}
--       (fⱽ : Hom[ C.id {x} ][ xᴰ , xᴰ' ])
--       (gⱽ : Hom[ C.id ][ xᴰ' , xᴰ'' ])
--       → Hom[ C.id ][ xᴰ , xᴰ'' ]
--     fⱽ ⋆ⱽ gⱽ = fⱽ ⋆ⱽᴰ gⱽ

--     _⋆ᴰⱽ_ : ∀ {x y} {xᴰ yᴰ yᴰ'}{f : C.Hom[ x , y ]}
--       (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
--       (gᴰ : Hom[ C.id ][ yᴰ , yᴰ' ])
--       → Hom[ f ][ xᴰ , yᴰ' ]
--     fᴰ ⋆ᴰⱽ gⱽ = reind (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ)

--     ≡in : {x y : Cob}{f g : C.Hom[ x , y ]}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
--       {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
--       {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
--       {p : f ≡ g}
--       → (fᴰ ≡[ p ] gᴰ)
--       → fᴰ ∫≡ gᴰ
--     ≡in = λ pᴰ → ΣPathP (_ , pᴰ)
--     opaque
--       ⋆IdLᴰᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
--         → (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
--         → idᴰ ⋆ᴰ fᴰ ∫≡ fᴰ
--       ⋆IdLᴰᴰ fᴰ = ⋆IdLᴰ fᴰ

--       ⋆IdRᴰᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
--         → (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
--         → Path (∫Hom[ _ , _ ])
--             (_ , (fᴰ ⋆ᴰ idᴰ))
--             (_ , fᴰ)
--       ⋆IdRᴰᴰ fᴰ = ⋆IdRᴰ fᴰ

--       ⋆Assocᴰᴰᴰ : ∀ {w x y z wᴰ xᴰ yᴰ zᴰ}
--         {f : C.Hom[ w , x ]}
--         {g : C.Hom[ x , y ]}
--         {h : C.Hom[ y , z ]}
--         (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
--         (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
--         (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
--         → Path ∫Hom[ _ , _ ]
--             (_ , (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ)
--             (_ , fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ))
--       ⋆Assocᴰᴰᴰ fᴰ gᴰ hᴰ = ⋆Assocᴰ fᴰ gᴰ hᴰ

--       isSetDepHomᴰ : ∀ {x y xᴰ yᴰ} →
--         isSetDep (λ (f : C.Hom[ x , y ]) → Hom[ f ][ xᴰ , yᴰ ])
--       isSetDepHomᴰ = isSet→isSetDep (λ f → isSetHomᴰ)

--       isSetHomᴰ' : ∀ {x y}{xᴰ}{yᴰ}
--         {f g : C.Hom[ x , y ]} {p q : f ≡ g}
--         (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
--         (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
--         (pᴰ : fᴰ ≡[ p ] gᴰ )
--         (qᴰ : fᴰ ≡[ q ] gᴰ )
--         → ∀ i j → Hom[  C.isSetHom f g p q i j ][ xᴰ , yᴰ ]
--       isSetHomᴰ' fᴰ gᴰ pᴰ qᴰ i j = isSetDepHomᴰ fᴰ gᴰ pᴰ qᴰ (C.isSetHom _ _ _ _) i j

--       ≡out : {x y : Cob}{f g : C.Hom[ x , y ]}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
--         {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
--         {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
--         → (ppᴰ : Path ∫Hom[ _ , _ ] (_ , fᴰ) (_ , gᴰ))
--         → (fᴰ ≡[ fst (PathPΣ ppᴰ) ] gᴰ)
--       ≡out e = snd (PathPΣ e)

--       rectify : {x y : Cob}{f g : C.Hom[ x , y ]}{p p' : f ≡ g}
--         {xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
--         {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
--         {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
--         → fᴰ ≡[ p ] gᴰ → fᴰ ≡[ p' ] gᴰ
--       rectify {fᴰ = fᴰ}{gᴰ} pᴰ = subst (fᴰ ≡[_] gᴰ) (C.isSetHom _ _ _ _) pᴰ

--       reind-filler : {x y : Cob}{f g : C.Hom[ x , y ]}
--         {xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
--         (p : f ≡ g)
--         (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
--         → Path (∫Hom[ _ , _ ]) (f , fᴰ) (g , reind p fᴰ)
--       reind-filler p fᴰ = ΣPathP (p , subst-filler Hom[_][ _ , _ ] p fᴰ)

--       reind-cong : ∀ {x y xᴰ yᴰ}{f f' g g' : C.Hom[ x , y ]}
--         {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
--         {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
--         (p : f ≡ f')
--         (q : g ≡ g')
--         → Path ∫Hom[ _ , _ ]
--             (_ , fᴰ)
--             (_ , gᴰ)
--         → Path ∫Hom[ _ , _ ]
--             (_ , reind p fᴰ)
--             (_ , reind q gᴰ)
--       reind-cong p q fᴰ≡gᴰ = sym (reind-filler _ _) ∙ fᴰ≡gᴰ ∙ reind-filler _ _

--     ∫C : Category (Σω[ x ∈ Cob ] ob[ x ]) _
--     ∫C .Hom[_,_] = ∫Hom[_,_]
--     ∫C .id = _ , idᴰ
--     ∫C ._⋆_ ffᴰ ggᴰ = _ , (ffᴰ .snd ⋆ᴰ ggᴰ .snd)
--     ∫C .⋆IdL ffᴰ = ⋆IdLᴰᴰ _
--     ∫C .⋆IdR ffᴰ = ⋆IdRᴰᴰ _
--     ∫C .⋆Assoc ffᴰ ggᴰ hhᴰ = ⋆Assocᴰᴰᴰ _ _ _
--     ∫C .isSetHom = isSetΣ C.isSetHom (λ _ → isSetHomᴰ)

--     private
--       module ∫C = CategoryNotation ∫C
--     opaque
--       ⋆IdLⱽᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
--         → (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
--         → idᴰ ⋆ⱽᴰ fᴰ ∫≡ fᴰ
--       ⋆IdLⱽᴰ fᴰ = sym (reind-filler _ _) ∙ ⋆IdLᴰᴰ fᴰ

--       ⋆IdLⱽⱽ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
--         → idᴰ ⋆ⱽ fⱽ ∫≡ fⱽ
--       ⋆IdLⱽⱽ = ⋆IdLⱽᴰ

--       ⋆IdLᴰⱽ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
--         → idᴰ ⋆ᴰⱽ fⱽ ∫≡ fⱽ
--       ⋆IdLᴰⱽ = λ fᴰ → sym (reind-filler _ _) ∙ ⋆IdLᴰᴰ fᴰ

--       ⋆IdRᴰⱽ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}(fᴰ : Hom[ f ][ xᴰ , yᴰ ])
--         → fᴰ ⋆ᴰⱽ idᴰ ∫≡ fᴰ
--       ⋆IdRᴰⱽ = λ fᴰ → sym (reind-filler _ _) ∙ ⋆IdRᴰᴰ fᴰ

--       ⋆IdRⱽᴰ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
--         → fⱽ ⋆ⱽᴰ idᴰ ∫≡ fⱽ
--       ⋆IdRⱽᴰ = λ fᴰ → sym (reind-filler _ _) ∙ ⋆IdRᴰᴰ fᴰ

--       ⋆IdRⱽⱽ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
--         → fⱽ ⋆ⱽ idᴰ ∫≡ fⱽ
--       ⋆IdRⱽⱽ fⱽ = ⋆IdRⱽᴰ fⱽ

--       ⋆Assocⱽᴰᴰ : ∀ {x y z wᴰ xᴰ yᴰ zᴰ}
--         {g : C.Hom[ x , y ]}
--         {h : C.Hom[ y , z ]}
--         (fⱽ : Hom[ C.id {x} ][ wᴰ , xᴰ ])
--         (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
--         (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
--         → (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰ hᴰ ∫≡ fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰ hᴰ)
--       ⋆Assocⱽᴰᴰ _ _ _ = ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ reind-filler _ _

--       ⋆Assocᴰⱽᴰ : ∀ {w x z wᴰ xᴰ yᴰ zᴰ}
--         {f : C.Hom[ w , x ]}
--         {h : C.Hom[ x , z ]}
--         (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
--         (gⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
--         (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
--         → Path ∫Hom[ _ , _ ]
--             (_ , (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰ hᴰ)
--             (_ , fᴰ ⋆ᴰ (gⱽ ⋆ⱽᴰ hᴰ))
--       ⋆Assocᴰⱽᴰ fᴰ gⱽ hᴰ = ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩

--       ⋆Assocᴰᴰⱽ : ∀ {w x y wᴰ xᴰ yᴰ zᴰ}
--         {f : C.Hom[ w , x ]}
--         {g : C.Hom[ x , y ]}
--         (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
--         (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
--         (hⱽ : Hom[ C.id ][ yᴰ , zᴰ ])
--         → Path ∫Hom[ _ , _ ]
--             (_ , (fᴰ ⋆ᴰ gᴰ) ⋆ᴰⱽ hⱽ)
--             (_ , fᴰ ⋆ᴰ (gᴰ ⋆ᴰⱽ hⱽ))
--       ⋆Assocᴰᴰⱽ fᴰ gᴰ hⱽ = (sym $ reind-filler _ _) ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩

--       ⋆Assocⱽⱽᴰ : ∀ {y z wᴰ xᴰ yᴰ zᴰ}
--         {h : C.Hom[ y , z ]}
--         (fⱽ : Hom[ C.id ][ wᴰ , xᴰ ])
--         (gⱽ : Hom[ C.id ][ xᴰ , yᴰ ])
--         (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
--         → Path ∫Hom[ _ , _ ]
--             (_ , (fⱽ ⋆ⱽ gⱽ) ⋆ⱽᴰ hᴰ)
--             (_ , fⱽ ⋆ⱽᴰ (gⱽ ⋆ⱽᴰ hᴰ))
--       ⋆Assocⱽⱽᴰ fⱽ gⱽ hᴰ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

--       ⋆Assocⱽᴰⱽ : ∀ {x y wᴰ xᴰ yᴰ zᴰ}
--         {g : C.Hom[ x , y ]}
--         (fⱽ : Hom[ C.id ][ wᴰ , xᴰ ])
--         (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
--         (hⱽ : Hom[ C.id ][ yᴰ , zᴰ ])
--         → Path ∫Hom[ _ , _ ]
--             (_ , (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰⱽ hⱽ)
--             (_ , fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰⱽ hⱽ))
--       ⋆Assocⱽᴰⱽ fⱽ gᴰ hⱽ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

--       ⋆Assocᴰⱽⱽ : ∀ {w x wᴰ xᴰ yᴰ zᴰ}
--         {f : C.Hom[ w , x ]}
--         (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
--         (gⱽ : Hom[ C.id ][ xᴰ , yᴰ ])
--         (hⱽ : Hom[ C.id ][ yᴰ , zᴰ ])
--         → Path ∫Hom[ _ , _ ]
--             (_ , (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰⱽ hⱽ)
--             (_ , fᴰ ⋆ᴰⱽ (gⱽ ⋆ⱽ hⱽ))
--       ⋆Assocᴰⱽⱽ fᴰ gⱽ hⱽ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

--       ⋆Assocⱽⱽⱽ : ∀ {x wᴰ xᴰ yᴰ zᴰ}
--         (fⱽ : Hom[ C .id {x} ][ wᴰ , xᴰ ])
--         (gⱽ : Hom[ C .id ][ xᴰ , yᴰ ])
--         (hⱽ : Hom[ C .id ][ yᴰ , zᴰ ])
--         → Path ∫Hom[ _ , _ ]
--             (_ , (fⱽ ⋆ⱽ gⱽ) ⋆ⱽ hⱽ)
--             (_ , fⱽ ⋆ⱽ (gⱽ ⋆ⱽ hⱽ))
--       ⋆Assocⱽⱽⱽ fⱽ gⱽ hⱽ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

--     v[_] : (x : Cob) → Category ob[ x ] (Hom-ℓᴰ x x)
--     v[ x ] .Hom[_,_] = Hom[ C.id ][_,_]
--     v[ x ] .id = idᴰ
--     v[ x ] ._⋆_ fⱽ gⱽ = fⱽ ⋆ⱽ gⱽ
--     v[ x ] .⋆IdL fⱽ = rectify $ ≡out $ ⋆IdLⱽⱽ _
--     v[ x ] .⋆IdR fⱽ = rectify $ ≡out $ ⋆IdRⱽⱽ _
--     v[ x ] .⋆Assoc fⱽ gⱽ hⱽ = rectify $ ≡out $ ⋆Assocⱽⱽⱽ _ _ _
--     v[ x ] .isSetHom = isSetHomᴰ

--     module Cⱽ {x : Cob} = Category (v[ x ])
--     open ∫C public

-- open Categoryᴰ

-- -- Displayed categories whose fibers are *small* categories.
-- -- This means:
-- -- 1. The type of displayed objects over any fixed object is small
-- -- 2. The type of displayed hom sets is small and the level only
-- -- depends on the base objects.
-- module _ (C : Category Cob C-ℓ) where
--   private
--     module C = Category C
--   module _ (obᴰ-ℓ : Cob → Level) (obᴰ : ∀ x → Type (obᴰ-ℓ x))
--     (Homᴰ-ℓ : ∀ (x y : Cob) → Level) where
--     SmallFibersCategoryᴰ : Typeω
--     SmallFibersCategoryᴰ = Categoryᴰ C (λ x → Liftω (obᴰ x)) λ x y _ _ → Homᴰ-ℓ x y

-- module _ {C : Category Cob C-ℓ} {Cobᴰ}{Cᴰ-ℓ} (Cᴰ : SmallFibersCategoryᴰ C Cobᴰ-ℓ Cobᴰ Cᴰ-ℓ) where
--   private
--     module Cᴰ = Categoryᴰ Cᴰ
--   SmallFiber : (x : Cob) → Small.Category (Cobᴰ-ℓ x) (Cᴰ-ℓ x x)
--   SmallFiber x = SmallLocallySmallCategory→SmallCategory ((liftω (Cobᴰ x)) , Cᴰ.v[ x ])

-- -- Instances
-- module _ {C : Category Cob C-ℓ}(Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ) where
--   private
--     module C = CategoryNotation C
--     module Cᴰ = Categoryᴰ Cᴰ
--   module _ {Cobᴰᴰ CHom-ℓᴰᴰ}(Cᴰᴰ : Categoryᴰ Cᴰ.∫C Cobᴰᴰ CHom-ℓᴰᴰ) where
--     private
--       module Cᴰᴰ = Categoryᴰ Cᴰᴰ
--     ∫Cᴰ : Categoryᴰ C (λ x → Σω[ xᴰ ∈ Cobᴰ x ] Cobᴰᴰ (x , xᴰ)) _
--     ∫Cᴰ .Hom[_][_,_] f xᴰxᴰᴰ yᴰyᴰᴰ =
--       Σ[ fᴰ ∈ Cᴰ.Hom[ f ][ xᴰxᴰᴰ .fst , yᴰyᴰᴰ .fst ] ]
--         Cᴰᴰ.Hom[ f , fᴰ ][ xᴰxᴰᴰ .snd , yᴰyᴰᴰ .snd ]
--     ∫Cᴰ .idᴰ = Cᴰ.idᴰ , Cᴰᴰ.idᴰ
--     ∫Cᴰ ._⋆ᴰ_ ffᴰ ggᴰ = (ffᴰ .fst Cᴰ.⋆ᴰ ggᴰ .fst) , (ffᴰ .snd Cᴰᴰ.⋆ᴰ ggᴰ .snd)
--     ∫Cᴰ .⋆IdLᴰ ffᴰ =
--       ΣPathP ((C.⋆IdL _) , (
--       ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ (ffᴰ .fst)) ,
--       (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $ Cᴰᴰ.⋆IdLᴰ (ffᴰ .snd)))))
--     ∫Cᴰ .⋆IdRᴰ ffᴰ =
--       ΣPathP ((C.⋆IdR _) , (
--       ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdRᴰ (ffᴰ .fst)) ,
--       (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $ Cᴰᴰ.⋆IdRᴰ (ffᴰ .snd)))))
--     ∫Cᴰ .⋆Assocᴰ ffᴰ ggᴰ hhᴰ =
--       ΣPathP (C.⋆Assoc _ _ _ ,
--       (ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assoc _ _ _) ,
--       (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $ Cᴰᴰ.⋆Assoc _ _ _))))
--     ∫Cᴰ .isSetHomᴰ = isSetΣ Cᴰ.isSetHomᴰ (λ _ → Cᴰᴰ.isSetHomᴰ)

--   record CatIsoᴰ {x y : Cob}(f : C.ISOC.Hom[ x , y ]) (xᴰ : Cobᴰ x ) (yᴰ : Cobᴰ y)
--     : Type (ℓ-max (C-ℓ x x) $
--             ℓ-max (C-ℓ x y) $
--             ℓ-max (C-ℓ y x) $
--             ℓ-max (C-ℓ y y) $
--             ℓ-max (CHom-ℓᴰ x x xᴰ xᴰ) $
--             ℓ-max (CHom-ℓᴰ x y xᴰ yᴰ) $
--             ℓ-max (CHom-ℓᴰ y x yᴰ xᴰ) $
--             ℓ-max (CHom-ℓᴰ y y yᴰ yᴰ) $
--             ℓ-zero)
--     where
--     no-eta-equality
--     constructor isoᴰ
--     field
--       funᴰ : Cᴰ.Hom[ f .CatIso.fun ][ xᴰ , yᴰ ]
--       invᴰ : Cᴰ.Hom[ f .CatIso.inv ][ yᴰ , xᴰ ]
--       secᴰ : Path Cᴰ.Hom[ _ , _ ] (_ , invᴰ Cᴰ.⋆ᴰ funᴰ) (_ , Cᴰ.idᴰ)
--       retᴰ : Path Cᴰ.Hom[ _ , _ ] (_ , funᴰ Cᴰ.⋆ᴰ invᴰ) (_ , Cᴰ.idᴰ)

--   CatIsoᴰIsoΣ : ∀ {x y}{f : C.ISOC.Hom[ x , y ]}{xᴰ yᴰ}
--     → Iso (CatIsoᴰ f xᴰ yᴰ)
--           (Σ[ funᴰ ∈ Cᴰ.Hom[ f .CatIso.fun ][ xᴰ , yᴰ ] ]
--           Σ[ invᴰ ∈ Cᴰ.Hom[ f .CatIso.inv ][ yᴰ , xᴰ ] ]
--           Path Cᴰ.Hom[ _ , _ ] (_ , invᴰ Cᴰ.⋆ᴰ funᴰ) (_ , Cᴰ.idᴰ)
--           × Path Cᴰ.Hom[ _ , _ ] (_ , funᴰ Cᴰ.⋆ᴰ invᴰ) (_ , Cᴰ.idᴰ))
--   unquoteDef CatIsoᴰIsoΣ = defineRecordIsoΣ CatIsoᴰIsoΣ (quote (CatIsoᴰ))

--   ∫CatIso : {x y : Cob}{f : C.ISOC.Hom[ x , y ]} {xᴰ : Cobᴰ x}{yᴰ : Cobᴰ y}
--     → (fᴰ : CatIsoᴰ f xᴰ yᴰ)
--     → Cᴰ.ISOC.Hom[ (_ , xᴰ) , (_ , yᴰ) ]
--   ∫CatIso fᴰ .CatIso.fun = _ , fᴰ .CatIsoᴰ.funᴰ
--   ∫CatIso fᴰ .CatIso.inv = _ , fᴰ .CatIsoᴰ.invᴰ
--   ∫CatIso fᴰ .CatIso.sec = fᴰ .CatIsoᴰ.secᴰ
--   ∫CatIso fᴰ .CatIso.ret = fᴰ .CatIsoᴰ.retᴰ

--   isIsoᴰ : ∀ {x y}{f : C.Hom[ x , y ]}(f⁻ : isIso C f)
--     {xᴰ yᴰ}(funᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
--     → Type _
--   isIsoᴰ f⁻ funᴰ = Σ[ invᴰ ∈ Cᴰ.Hom[ f⁻ .fst ][ _ , _ ] ]
--     Path Cᴰ.Hom[ _ , _ ] (_ , invᴰ Cᴰ.⋆ᴰ funᴰ) (_ , Cᴰ.idᴰ)
--     × Path Cᴰ.Hom[ _ , _ ] (_ , funᴰ Cᴰ.⋆ᴰ invᴰ) (_ , Cᴰ.idᴰ)

--   module _ {x y : Cob}{f g : C.ISOC.Hom[ x , y ]}
--     {xᴰ yᴰ}{fᴰ : CatIsoᴰ f xᴰ yᴰ}{gᴰ : CatIsoᴰ g xᴰ yᴰ}
--     (fᴰfunᴰ≡gᴰfunᴰ : Path Cᴰ.Hom[ _ , _ ]
--         (_ , fᴰ .CatIsoᴰ.funᴰ)
--         (_ , gᴰ .CatIsoᴰ.funᴰ))
--     where
--     private
--       ∫fᴰ≡∫gᴰ : Path Cᴰ.ISOC.Hom[ (x , xᴰ) , (y , yᴰ) ] (∫CatIso fᴰ) (∫CatIso gᴰ)
--       ∫fᴰ≡∫gᴰ = Cᴰ.ISOC≡ fᴰfunᴰ≡gᴰfunᴰ
--     opaque
--       CatIsoᴰ≡ :
--         Path (Σ[ f ∈ C.ISOC.Hom[ x , y ] ] CatIsoᴰ f xᴰ yᴰ)
--             (_ , fᴰ)
--             (_ , gᴰ)
--       CatIsoᴰ≡ = ΣPathP (f≡g , fᴰ≡gᴰ) where
--         f≡g : f ≡ g
--         f≡g i .CatIso.fun = ∫fᴰ≡∫gᴰ i .CatIso.fun .fst
--         f≡g i .CatIso.inv = ∫fᴰ≡∫gᴰ i .CatIso.inv .fst
--         f≡g i .CatIso.sec = isSet→Square C.isSetHom
--           C.⟨ (λ i → ∫fᴰ≡∫gᴰ i .CatIso.inv .fst) ⟩⋆⟨ (λ i → ∫fᴰ≡∫gᴰ i .CatIso.fun .fst) ⟩
--           (refl {x = C.id {y}})
--           (f .CatIso.sec)
--           ((g .CatIso.sec))
--           i
--         f≡g i .CatIso.ret = isSet→Square C.isSetHom
--           C.⟨ (λ i → ∫fᴰ≡∫gᴰ i .CatIso.fun .fst) ⟩⋆⟨ (λ i → ∫fᴰ≡∫gᴰ i .CatIso.inv .fst) ⟩
--           (refl {x = C.id {x}})
--           (f .CatIso.ret)
--           (g .CatIso.ret)
--           i
--         fᴰ≡gᴰ : PathP (λ i → CatIsoᴰ (f≡g i) xᴰ yᴰ) fᴰ gᴰ
--         fᴰ≡gᴰ i .CatIsoᴰ.funᴰ = ∫fᴰ≡∫gᴰ i .CatIso.fun .snd
--         fᴰ≡gᴰ i .CatIsoᴰ.invᴰ = ∫fᴰ≡∫gᴰ i .CatIso.inv .snd
--         fᴰ≡gᴰ i .CatIsoᴰ.secᴰ = ∫fᴰ≡∫gᴰ i .CatIso.sec
--         fᴰ≡gᴰ i .CatIsoᴰ.retᴰ = ∫fᴰ≡∫gᴰ i .CatIso.ret

--       CatIsoᴰPathP : ∀ {f≡g : f ≡ g}
--         → PathP (λ i → CatIsoᴰ (f≡g i) xᴰ yᴰ) fᴰ gᴰ
--       CatIsoᴰPathP {f≡g} =
--         TypeRectify (λ j i → CatIsoᴰ (lem j i) xᴰ yᴰ)
--           (PathPΣ CatIsoᴰ≡ .snd)
--         where
--           lem : (PathPΣ CatIsoᴰ≡ .fst) ≡ f≡g
--           lem = C.ISOC.isSetHom _ _ _ _

--   idCatIsoᴰ : ∀ {x}{xᴰ : Cobᴰ x} → CatIsoᴰ C.ISOC.id xᴰ xᴰ
--   idCatIsoᴰ .CatIsoᴰ.funᴰ = Cᴰ.idᴰ
--   idCatIsoᴰ .CatIsoᴰ.invᴰ = Cᴰ.idᴰ
--   idCatIsoᴰ .CatIsoᴰ.secᴰ = Cᴰ.⋆IdL _
--   idCatIsoᴰ .CatIsoᴰ.retᴰ = Cᴰ.⋆IdL _

--   ⋆CatIsoᴰ : ∀ {x y z xᴰ yᴰ zᴰ}
--     {f : CatIso C x y}
--     {g : CatIso C y z}
--     (fᴰ : CatIsoᴰ f xᴰ yᴰ)
--     (gᴰ : CatIsoᴰ g yᴰ zᴰ)
--     → CatIsoᴰ (f C.ISOC.⋆ g) xᴰ zᴰ
--   ⋆CatIsoᴰ fᴰ gᴰ = isoᴰ
--     (∫fᴰ⋆∫gᴰ .CatIso.fun .snd)
--     (∫fᴰ⋆∫gᴰ .CatIso.inv .snd)
--     (∫fᴰ⋆∫gᴰ .CatIso.sec)
--     (∫fᴰ⋆∫gᴰ .CatIso.ret)
--     where
--     ∫fᴰ⋆∫gᴰ = ∫CatIso fᴰ Cᴰ.ISOC.⋆ ∫CatIso gᴰ

--   ISOᴰ : Categoryᴰ C.ISOC Cobᴰ _
--   ISOᴰ .Hom[_][_,_] = CatIsoᴰ
--   ISOᴰ .idᴰ = idCatIsoᴰ
--   ISOᴰ ._⋆ᴰ_ = ⋆CatIsoᴰ
--   ISOᴰ .⋆IdLᴰ fᴰ = CatIsoᴰ≡ (Cᴰ.⋆IdLᴰ (fᴰ .CatIsoᴰ.funᴰ))
--   ISOᴰ .⋆IdRᴰ fᴰ = CatIsoᴰ≡ (Cᴰ.⋆IdRᴰ (fᴰ .CatIsoᴰ.funᴰ))
--   ISOᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = CatIsoᴰ≡ $ Cᴰ.⋆Assocᴰ _ _ _
--   ISOᴰ .isSetHomᴰ = isSetIso CatIsoᴰIsoΣ (isSetΣ Cᴰ.isSetHomᴰ (λ _ → isSetΣ Cᴰ.isSetHomᴰ
--     λ _ → isProp→isSet (isProp× (Cᴰ.isSetHom _ _) (Cᴰ.isSetHom _ _))))

--   CatIsoⱽ : {x : Cob}(xᴰ yᴰ : Cobᴰ x) → Type _
--   CatIsoⱽ = CatIsoᴰ (idCatIso C)

--   CatIsoⱽ→CatIsoFiber : ∀ {x}{xᴰ yᴰ : Cobᴰ x}
--     (fⱽ : CatIsoⱽ xᴰ yᴰ)
--     → CatIso Cᴰ.v[ x ] xᴰ yᴰ
--   CatIsoⱽ→CatIsoFiber fⱽ .CatIso.fun = fⱽ .CatIsoᴰ.funᴰ
--   CatIsoⱽ→CatIsoFiber fⱽ .CatIso.inv = fⱽ .CatIsoᴰ.invᴰ
--   CatIsoⱽ→CatIsoFiber fⱽ .CatIso.sec = Cᴰ.rectify $ Cᴰ.≡out $
--     sym (Cᴰ.reind-filler _ _) ∙ fⱽ .CatIsoᴰ.secᴰ
--   CatIsoⱽ→CatIsoFiber fⱽ .CatIso.ret = Cᴰ.rectify $ Cᴰ.≡out $
--     sym (Cᴰ.reind-filler _ _) ∙ fⱽ .CatIsoᴰ.retᴰ

--   module CategoryᴰNotation where
--     open Categoryᴰ Cᴰ public
--     ISOCᴰ = ISOᴰ
--     module ISOCᴰ = Categoryᴰ ISOᴰ
--     ISOCᴰ≡ :
--       ∀ {x y : Cob}{f g : C.ISOC.Hom[ x , y ]}
--       {xᴰ yᴰ}{fᴰ : ISOCᴰ.Hom[ f ][ xᴰ , yᴰ ]}{gᴰ : ISOCᴰ.Hom[ g ][ xᴰ , yᴰ ]}
--       → fᴰ .CatIsoᴰ.funᴰ Cᴰ.∫≡ gᴰ .CatIsoᴰ.funᴰ
--       → fᴰ ISOCᴰ.∫≡ gᴰ
--     ISOCᴰ≡ = CatIsoᴰ≡

--     invCatIsoᴰ : ∀ {x y xᴰ yᴰ}{f : C.ISOC.Hom[ x , y ]}
--       → (fᴰ : CatIsoᴰ f xᴰ yᴰ)
--       → CatIsoᴰ (C.invCatIso f) yᴰ xᴰ
--     invCatIsoᴰ fᴰ .CatIsoᴰ.funᴰ = fᴰ .CatIsoᴰ.invᴰ
--     invCatIsoᴰ fᴰ .CatIsoᴰ.invᴰ = fᴰ .CatIsoᴰ.funᴰ
--     invCatIsoᴰ fᴰ .CatIsoᴰ.secᴰ = fᴰ .CatIsoᴰ.retᴰ
--     invCatIsoᴰ fᴰ .CatIsoᴰ.retᴰ = fᴰ .CatIsoᴰ.secᴰ

--     -- Can probably get this from ∫ somehow
--     CatIsoᴰ⋆ᴰ-Iso-over : ∀ {x y xᴰ yᴰ}{f : C.ISOC.Hom[ x , y ]}
--       → CatIsoᴰ f xᴰ yᴰ
--       → ∀ {z}{zᴰ : Cobᴰ z}
--       → IsoOver (C.CatIso⋆-Iso f) Cᴰ.Hom[_][ yᴰ , zᴰ ] Cᴰ.Hom[_][ xᴰ , zᴰ ]
--     CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.fun g gᴰ = fᴰ .CatIsoᴰ.funᴰ Cᴰ.⋆ᴰ gᴰ
--     CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.inv g gᴰ = fᴰ .CatIsoᴰ.invᴰ Cᴰ.⋆ᴰ gᴰ
--     CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.rightInv g gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
--       sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ fᴰ .CatIsoᴰ.retᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdL _
--     CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.leftInv g gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
--       sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ fᴰ .CatIsoᴰ.secᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdL _

-- -- Variants of smallness for displayed categories.
-- -- SmallObjectsCategoryᴰ
-- --   : ∀ (C : Category Cob C-ℓ)
-- --   → {ℓC}(ob : Type ℓC)(C-ℓ : ob → ob → Level)
-- --   → Typeω
-- -- SmallObjectsCategoryᴰ ob C-ℓ = Category (Liftω ob) λ (liftω x) (liftω y) → C-ℓ x y

-- -- -- A (LS) Category such that all hom sets are at the *same* universe level
-- -- GloballySmallCategory : (Cob : Typeω)(ℓC' : Level) → Typeω
-- -- GloballySmallCategory Cob ℓC' = Category Cob λ _ _ → ℓC'

-- -- -- A category is small if it both has small objects and is globally
-- -- -- small.
-- -- -- This is the only variant that is itself a small type: the
-- -- -- definition of Category in Cubical.Categories.Category
-- -- SmallCategory : ∀ ℓC (ℓC' : Level) → Typeω
-- -- SmallCategory ℓC ℓC' = Σω[ (liftω ob) ∈ Liftω (Type ℓC) ] GloballySmallCategory (Liftω ob) ℓC'

-- Indiscrete : (ob : Typeω) → GloballySmallCategory ob ℓ-zero
-- Indiscrete ob .Hom[_,_] = λ _ _ → Unit
-- Indiscrete ob .id = tt
-- Indiscrete ob ._⋆_ = λ f g → tt
-- Indiscrete ob .⋆IdL = λ _ → refl
-- Indiscrete ob .⋆IdR = λ _ → refl
-- Indiscrete ob .⋆Assoc = λ _ _ _ → refl
-- Indiscrete ob .isSetHom = isSetUnit

-- UNIT : GloballySmallCategory (Liftω Unit) ℓ-zero
-- UNIT = Indiscrete (Liftω Unit)

-- SmallUNIT : SmallCategory ℓ-zero ℓ-zero
-- SmallUNIT = _ , UNIT

-- -- module _ {Dob} (C : Small.Category ℓC ℓC') (D : Category Dob) where
-- --   private
-- --     module C = Small.Category C
-- --     module D = CategoryNotation D
-- --   _⊘_ : ?
-- --   _⊘_ = ?
-- -- --   _⊘_ : Category (C .Category.ob ×ω Dob)
-- -- --   -- This is inferrable
-- -- --   _⊘_ .Hom-ℓ = λ (_ , y) (_ , y') → ℓ-max ℓC' (D.Hom-ℓ y y')
-- -- --   _⊘_ .Hom[_,_] (x , y) (x' , y') = C.Hom[ x , x' ] × D.Hom[ y , y' ]
-- -- --   _⊘_ .id = C.id , D.id
-- -- --   _⊘_ ._⋆_ (f , g) (f' , g') = (f C.⋆ f') , (g D.⋆ g')
-- -- --   _⊘_ .⋆IdL (f , g) = ΣPathP (C.⋆IdL f , D.⋆IdL g)
-- -- --   _⊘_ .⋆IdR (f , g) = ΣPathP (C.⋆IdR f , D.⋆IdR g)
-- -- --   _⊘_ .⋆Assoc (f , g) (f' , g') (f'' , g'') = ΣPathP (C.⋆Assoc f f' f'' , D.⋆Assoc g g' g'')
-- -- --   _⊘_ .isSetHom = isSet× C.isSetHom D.isSetHom

-- -- --   private
-- -- --     module ⊘ = LocallySmallCategoryNotation _⊘_
-- -- --   ⊘-iso : ∀ {x y x' y'}
-- -- --     → (f : SmallCategory.CatIso C x x')
-- -- --     → (g : D.ISOC.Hom[ y , y' ])
-- -- --     → ⊘.ISOC.Hom[ (x , y) , (x' , y') ]
-- -- --   ⊘-iso f g .CatIso.fun = (f .fst) , (g .CatIso.fun)
-- -- --   ⊘-iso f g .CatIso.inv = (f .snd .SmallCategory.isIso.inv) , (g .CatIso.inv)
-- -- --   ⊘-iso f g .CatIso.sec = ΣPathP (f .snd .SmallCategory.isIso.sec , g .CatIso.sec)
-- -- --   ⊘-iso f g .CatIso.ret = ΣPathP (f .snd .SmallCategory.isIso.ret , g .CatIso.ret)

-- -- TODO: make into a general indiscrete category construction
-- LEVEL : Small.Category ℓ-zero ℓ-zero
-- LEVEL .Small.Category.ob = Level
-- LEVEL .Small.Category.Hom[_,_] = λ _ _ → Unit
-- LEVEL .Small.Category.id = tt
-- LEVEL .Small.Category._⋆_ = λ f g → tt
-- LEVEL .Small.Category.⋆IdL = λ _ → refl
-- LEVEL .Small.Category.⋆IdR = λ _ → refl
-- LEVEL .Small.Category.⋆Assoc = λ _ _ _ → refl
-- LEVEL .Small.Category.isSetHom = isSetUnit

-- LEVELω : SmallCategory ℓ-zero ℓ-zero
-- LEVELω = mkSmallCategory LEVEL

-- -- -- LEVEL-iso : ∀ {ℓ} {ℓ'} → SmallCategory.CatIso LEVEL ℓ ℓ'
-- -- -- LEVEL-iso .fst = tt
-- -- -- LEVEL-iso .snd .SmallCategory.isIso.inv = tt
-- -- -- LEVEL-iso .snd .SmallCategory.isIso.sec = refl
-- -- -- LEVEL-iso .snd .SmallCategory.isIso.ret = refl

-- -- -- LEVELω-iso : ∀ {ℓ} {ℓ'} → CatIso LEVELω ℓ ℓ'
-- -- -- LEVELω-iso .CatIso.fun = tt
-- -- -- LEVELω-iso .CatIso.inv = tt
-- -- -- LEVELω-iso .CatIso.sec = refl
-- -- -- LEVELω-iso .CatIso.ret = refl

-- SET : SmallFibersCategoryᴰ (LEVELω .snd) _ (λ (liftω ℓ) → hSet ℓ) _
-- SET .Hom[_][_,_] _ (liftω X) (liftω Y) = ⟨ X ⟩ → ⟨ Y ⟩
-- SET .idᴰ = λ z → z
-- SET ._⋆ᴰ_ = λ g f x → f (g x)
-- SET .⋆IdLᴰ = λ _ → refl
-- SET .⋆IdRᴰ = λ _ → refl
-- SET .⋆Assocᴰ = λ _ _ _ → refl
-- SET .isSetHomᴰ {yᴰ = (liftω Y)} = isSet→ (Y .snd)

-- module _ (C : Category Cob C-ℓ)(D : Category Dob D-ℓ) where
--   private
--     module C = CategoryNotation C
--     module D = CategoryNotation D
--   weaken : Categoryᴰ C (λ _ → Dob) _
--   weaken .Hom[_][_,_] = λ _ → D.Hom[_,_]
--   weaken .idᴰ = D.id
--   weaken ._⋆ᴰ_ = D._⋆_
--   weaken .⋆IdLᴰ = λ f → ≡-× (C.⋆IdL _) (D.⋆IdL f)
--   weaken .⋆IdRᴰ = λ f → ≡-× (C.⋆IdR _) (D.⋆IdR f)
--   weaken .⋆Assocᴰ = λ f g h → ≡-× (C.⋆Assoc _ _ _) (D.⋆Assoc f g h)
--   weaken .isSetHomᴰ = D.isSetHom

-- -- -- -- module SET = LocallySmallCategoryᴰNotation SET
-- -- -- -- -- The total category LocallySmallCategoryᴰ.∫C SET is the "large category of all small sets"
-- -- -- -- -- Then
-- -- -- -- SETᴰ : LocallySmallCategoryᴰ
-- -- -- --          (LEVEL ⊘ LocallySmallCategoryᴰ.∫C SET)
-- -- -- --          (λ (ℓᴰ , (_ , liftω X)) → Liftω (⟨ X ⟩ → hSet ℓᴰ))
-- -- -- -- SETᴰ .LocallySmallCategoryᴰ.Hom-ℓᴰ = _
-- -- -- -- SETᴰ .LocallySmallCategoryᴰ.Hom[_][_,_] (_ , _ , f) (liftω Xᴰ) (liftω Yᴰ) =
-- -- -- --   ∀ x → ⟨ Xᴰ x ⟩ → ⟨ Yᴰ (f x ) ⟩
-- -- -- -- SETᴰ .LocallySmallCategoryᴰ.idᴰ = λ x xᴰ → xᴰ
-- -- -- -- SETᴰ .LocallySmallCategoryᴰ._⋆ᴰ_ {f = (_ , _ , f)} fᴰ gᴰ x xᴰ =
-- -- -- --   gᴰ (f x) (fᴰ x xᴰ)
-- -- -- -- SETᴰ .LocallySmallCategoryᴰ.⋆IdLᴰ = λ _ → refl
-- -- -- -- SETᴰ .LocallySmallCategoryᴰ.⋆IdRᴰ = λ _ → refl
-- -- -- -- SETᴰ .LocallySmallCategoryᴰ.⋆Assocᴰ = λ _ _ _ → refl
-- -- -- -- SETᴰ .LocallySmallCategoryᴰ.isSetHomᴰ {yᴰ = liftω Yᴰ} =
-- -- -- --   isSetΠ λ _ → isSet→ (Yᴰ _ .snd)

-- -- -- -- module SETᴰ = LocallySmallCategoryᴰNotation SETᴰ

-- -- -- -- module _ (C : LocallySmallCategory Cob) (D : LocallySmallCategory Dob) where
-- -- -- --   private
-- -- -- --     module D = LocallySmallCategory D
-- -- -- --   weaken : LocallySmallCategoryᴰ C λ _ → Dob
-- -- -- --   weaken .LocallySmallCategoryᴰ.Hom-ℓᴰ _ x _ y = D.Hom-ℓ x y
-- -- -- --   weaken .LocallySmallCategoryᴰ.Hom[_][_,_] _ = D.Hom[_,_]
-- -- -- --   weaken .LocallySmallCategoryᴰ.idᴰ = D.id
-- -- -- --   weaken .LocallySmallCategoryᴰ._⋆ᴰ_ = D._⋆_
-- -- -- --   weaken .LocallySmallCategoryᴰ.⋆IdLᴰ = D.⋆IdL
-- -- -- --   weaken .LocallySmallCategoryᴰ.⋆IdRᴰ = D.⋆IdR
-- -- -- --   weaken .LocallySmallCategoryᴰ.⋆Assocᴰ = D.⋆Assoc
-- -- -- --   weaken .LocallySmallCategoryᴰ.isSetHomᴰ = D.isSetHom
