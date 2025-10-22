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

⟨_⟩ob : ∀ {Cob}{CHom-ℓ} → Category Cob CHom-ℓ → Typeω
⟨_⟩ob {Cob = Cob} C = Cob

_^op : ∀ {Cob}{CHom-ℓ} → Category Cob CHom-ℓ → Category Cob λ x y → CHom-ℓ y x
(C ^op) .Hom[_,_] x y = C .Hom[_,_] y x
(C ^op) .id = C .id
(C ^op) ._⋆_ f g = C ._⋆_ g f
(C ^op) .⋆IdL = C .⋆IdR
(C ^op) .⋆IdR = C .⋆IdL
(C ^op) .⋆Assoc f g h = sym (C .⋆Assoc _ _ _)
(C ^op) .isSetHom = C .isSetHom

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

⟨_⟩small-ob : ∀ {ℓC ℓC'} → SmallCategory ℓC ℓC' → Type ℓC
⟨ C ⟩small-ob = C .fst .lowerω

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
