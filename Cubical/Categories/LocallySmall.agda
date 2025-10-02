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

module Cubical.Categories.LocallySmall where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure


open import Cubical.Data.Prod using (_×ω_; _,_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Base hiding (PRESHEAFᴰ)
open import Cubical.Categories.Displayed.Presheaf.Morphism

private
  variable
    ℓ ℓ' ℓ1 ℓ2 ℓw ℓx ℓy ℓz ℓC ℓC' : Level
    ℓᴰ ℓᴰ' ℓ1ᴰ ℓ2ᴰ ℓwᴰ ℓxᴰ ℓyᴰ ℓzᴰ ℓCᴰ ℓCᴰ' : Level

open _×ω_

LEVEL : Category ℓ-zero ℓ-zero
LEVEL .Category.ob = Level
LEVEL .Category.Hom[_,_] = λ _ _ → Unit
LEVEL .Category.id = tt
LEVEL .Category._⋆_ = λ f g → tt
LEVEL .Category.⋆IdL = λ _ → refl
LEVEL .Category.⋆IdR = λ _ → refl
LEVEL .Category.⋆Assoc = λ _ _ _ → refl
LEVEL .Category.isSetHom = isSetUnit

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

-- A LocallySmallCategory has a "proper class" of objects, but small hom sets
record LocallySmallCategory (ob : Typeω): Typeω where
  field
    -- since we are in Typeω, there's no reason not to make Hom-ℓ a field
    Hom-ℓ : ob → ob → Level
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

open LocallySmallCategory

module _ (C : Category ℓC ℓC') where
  private
    module C = Category C
  CategoriesAreLocallySmall : LocallySmallCategory (Liftω C.ob)
  CategoriesAreLocallySmall .Hom-ℓ = λ _ _ → ℓC'
  CategoriesAreLocallySmall .Hom[_,_] x y = C.Hom[ x .lowerω , y .lowerω ]
  CategoriesAreLocallySmall .id = C.id
  CategoriesAreLocallySmall ._⋆_ = C._⋆_
  CategoriesAreLocallySmall .⋆IdL = C.⋆IdL
  CategoriesAreLocallySmall .⋆IdR = C.⋆IdR
  CategoriesAreLocallySmall .⋆Assoc = C.⋆Assoc
  CategoriesAreLocallySmall .isSetHom = C.isSetHom

LEVELω : LocallySmallCategory (Liftω Level)
LEVELω = CategoriesAreLocallySmall LEVEL

module _ {Dob} (C : Category ℓC ℓC') (D : LocallySmallCategory Dob) where
  private
    module C = Category C
    module D = LocallySmallCategory D
  _⊘_ : LocallySmallCategory (C .Category.ob ×ω Dob)
  -- This is inferrable
  _⊘_ .Hom-ℓ = λ (_ , y) (_ , y') → ℓ-max ℓC' (D.Hom-ℓ y y')
  _⊘_ .Hom[_,_] (x , y) (x' , y') = C.Hom[ x , x' ] × D.Hom[ y , y' ]
  _⊘_ .id = C.id , D.id
  _⊘_ ._⋆_ (f , g) (f' , g') = (f C.⋆ f') , (g D.⋆ g')
  _⊘_ .⋆IdL (f , g) = ΣPathP (C.⋆IdL f , D.⋆IdL g)
  _⊘_ .⋆IdR (f , g) = ΣPathP (C.⋆IdR f , D.⋆IdR g)
  _⊘_ .⋆Assoc (f , g) (f' , g') (f'' , g'') = ΣPathP (C.⋆Assoc f f' f'' , D.⋆Assoc g g' g'')
  _⊘_ .isSetHom = isSet× C.isSetHom D.isSetHom

-- The key thing we need is to be able to iterate the ∫C construction
module _ {ob}(C : LocallySmallCategory ob) where
  private
    module C = LocallySmallCategory C
  record LocallySmallCategoryᴰ (ob[_] : ob → Typeω) : Typeω where
    field
      Hom-ℓᴰ : (x : ob)(xᴰ : ob[ x ]) (y : ob)(yᴰ : ob[ y ]) → Level
      Hom[_][_,_] : ∀ {x y}(f : C.Hom[ x , y ])(xᴰ : ob[ x ])(yᴰ : ob[ y ]) → Type (Hom-ℓᴰ x xᴰ y yᴰ)
      idᴰ : ∀ {x} {p : ob[ x ]} → Hom[ C.id ][ p , p ]
      _⋆ᴰ_ : ∀ {x y z} {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]} {xᴰ yᴰ zᴰ}
        → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f C.⋆ g ][ xᴰ , zᴰ ]
    infixr 9 _⋆ᴰ_

    _≡[_]_ : ∀ {x y xᴰ yᴰ} {f g : C.Hom[ x , y ]}
      → (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (p : f ≡ g) (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
      → Type (Hom-ℓᴰ x xᴰ y yᴰ)
    _≡[_]_ {x} {y} {xᴰ} {yᴰ} fᴰ p gᴰ = PathP (λ i → Hom[ p i ][ xᴰ , yᴰ ]) fᴰ gᴰ

    infix 2 _≡[_]_

    field
      ⋆IdLᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → idᴰ ⋆ᴰ fᴰ ≡[ C.⋆IdL f ] fᴰ
      ⋆IdRᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → fᴰ ⋆ᴰ idᴰ ≡[ C.⋆IdR f ] fᴰ
      ⋆Assocᴰ : ∀ {x y z w} {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]}  {h : C.Hom[ z , w ]} {xᴰ yᴰ zᴰ wᴰ}
        (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ yᴰ , zᴰ ]) (hᴰ : Hom[ h ][ zᴰ , wᴰ ])
        → (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ ≡[ C.⋆Assoc f g h ] fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ)
      isSetHomᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} → isSet Hom[ f ][ xᴰ , yᴰ ]

    ∫Hom[_,_] : (x y : Σω ob ob[_]) → Type _
    ∫Hom[ xxᴰ , yyᴰ ] =
      Σ[ f ∈ C.Hom[ xxᴰ .fst , yyᴰ .fst ] ]
      Hom[ f ][ xxᴰ .snd , yyᴰ .snd ]

    -- Reindexing displayed morphisms along an equality in the base
    reind : {x y : ob}{f g : C.Hom[ x , y ]}
      {xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
      (p : f ≡ g)
      (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
      → Hom[ g ][ xᴰ , yᴰ ]
    reind = subst Hom[_][ _ , _ ]

    _⋆ⱽᴰ_ : ∀ {x y} {xᴰ xᴰ' yᴰ}{g : C.Hom[ x , y ]}
      (fⱽ : Hom[ C.id ][ xᴰ , xᴰ' ])
      (gᴰ : Hom[ g ][ xᴰ' , yᴰ ])
      → Hom[ g ][ xᴰ , yᴰ ]
    fⱽ ⋆ⱽᴰ gᴰ = reind (C.⋆IdL _) (fⱽ ⋆ᴰ gᴰ)

    _⋆ⱽ_ : ∀ {x} {xᴰ xᴰ' xᴰ''}
      (fⱽ : Hom[ C.id {x} ][ xᴰ , xᴰ' ])
      (gⱽ : Hom[ C.id ][ xᴰ' , xᴰ'' ])
      → Hom[ C.id ][ xᴰ , xᴰ'' ]
    fⱽ ⋆ⱽ gⱽ = fⱽ ⋆ⱽᴰ gⱽ

    _⋆ᴰⱽ_ : ∀ {x y} {xᴰ yᴰ yᴰ'}{f : C.Hom[ x , y ]}
      (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
      (gᴰ : Hom[ C.id ][ yᴰ , yᴰ' ])
      → Hom[ f ][ xᴰ , yᴰ' ]
    fᴰ ⋆ᴰⱽ gⱽ = reind (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ)

    ≡in : {x y : ob}{f g : C.Hom[ x , y ]}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
      {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
      {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
      {p : f ≡ g}
      → (fᴰ ≡[ p ] gᴰ)
      → Path ∫Hom[ _ , _ ] (_ , fᴰ) (_ , gᴰ)
    ≡in = λ pᴰ → ΣPathP (_ , pᴰ)
    ⋆IdLᴰᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
      → (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
      → Path (∫Hom[ _ , _ ])
          (_ , (idᴰ ⋆ᴰ fᴰ))
          (_ , fᴰ)
    ⋆IdLᴰᴰ fᴰ = ≡in (⋆IdLᴰ fᴰ)

    ⋆IdRᴰᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
      → (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
      → Path (∫Hom[ _ , _ ])
          (_ , (fᴰ ⋆ᴰ idᴰ))
          (_ , fᴰ)
    ⋆IdRᴰᴰ fᴰ = ≡in (⋆IdRᴰ fᴰ)

    ⋆Assocᴰᴰᴰ : ∀ {w x y z wᴰ xᴰ yᴰ zᴰ}
      {f : C.Hom[ w , x ]}
      {g : C.Hom[ x , y ]}
      {h : C.Hom[ y , z ]}
      (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
      (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
      (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
      → Path ∫Hom[ _ , _ ]
          (_ , (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ)
          (_ , fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ))
    ⋆Assocᴰᴰᴰ fᴰ gᴰ hᴰ = ≡in (⋆Assocᴰ fᴰ gᴰ hᴰ)

    opaque
      ≡out : {x y : ob}{f g : C.Hom[ x , y ]}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
        {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
        {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
        → (ppᴰ : Path ∫Hom[ _ , _ ] (_ , fᴰ) (_ , gᴰ))
        → (fᴰ ≡[ fst (PathPΣ ppᴰ) ] gᴰ)
      ≡out e = snd (PathPΣ e)

      rectify : {x y : ob}{f g : C.Hom[ x , y ]}{p p' : f ≡ g}
        {xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
        {fᴰ : Hom[ f ][ xᴰ , yᴰ ]}
        {gᴰ : Hom[ g ][ xᴰ , yᴰ ]}
        → fᴰ ≡[ p ] gᴰ → fᴰ ≡[ p' ] gᴰ
      rectify {fᴰ = fᴰ}{gᴰ} pᴰ = subst (fᴰ ≡[_] gᴰ) (C.isSetHom _ _ _ _) pᴰ

      reind-filler : {x y : ob}{f g : C.Hom[ x , y ]}
        {xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
        (p : f ≡ g)
        (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → Path (∫Hom[ _ , _ ]) (f , fᴰ) (g , reind p fᴰ)
      reind-filler p fᴰ = ΣPathP (p , subst-filler Hom[_][ _ , _ ] p fᴰ)

    ∫C : LocallySmallCategory (Σω[ x ∈ ob ] ob[ x ])
    ∫C .LocallySmallCategory.Hom-ℓ = _
    ∫C .LocallySmallCategory.Hom[_,_] = ∫Hom[_,_]
    ∫C .LocallySmallCategory.id = _ , idᴰ
    ∫C .LocallySmallCategory._⋆_ ffᴰ ggᴰ = _ , (ffᴰ .snd ⋆ᴰ ggᴰ .snd)
    ∫C .LocallySmallCategory.⋆IdL ffᴰ = ⋆IdLᴰᴰ _
    ∫C .LocallySmallCategory.⋆IdR ffᴰ = ⋆IdRᴰᴰ _
    ∫C .LocallySmallCategory.⋆Assoc ffᴰ ggᴰ hhᴰ = ⋆Assocᴰᴰᴰ _ _ _
    ∫C .LocallySmallCategory.isSetHom = isSetΣ C.isSetHom (λ _ → isSetHomᴰ)

    private
      module ∫C = LocallySmallCategory ∫C
    opaque
      ⋆IdLⱽᴰ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}
        → (fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → Path (∫Hom[ _ , _ ])
            (_ , (idᴰ ⋆ⱽᴰ fᴰ))
            (_ , fᴰ)
      ⋆IdLⱽᴰ fᴰ = sym (reind-filler _ _) ∙ ⋆IdLᴰᴰ fᴰ

      ⋆IdLⱽⱽ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
        → Path (∫Hom[ _ , _ ]) (_ , (idᴰ ⋆ⱽ fⱽ)) (_ , fⱽ)
      ⋆IdLⱽⱽ = ⋆IdLⱽᴰ

      ⋆IdLᴰⱽ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
        → Path (∫Hom[ _ , _ ]) (_ , (idᴰ ⋆ᴰⱽ fⱽ)) (_ , fⱽ)
      ⋆IdLᴰⱽ = λ fᴰ → sym (reind-filler _ _) ∙ ⋆IdLᴰᴰ fᴰ

      ⋆IdRᴰⱽ : ∀ {x y xᴰ yᴰ}{f : C.Hom[ x , y ]}(fᴰ : Hom[ f ][ xᴰ , yᴰ ])
        → Path (∫Hom[ _ , _ ]) (_ , (fᴰ ⋆ᴰⱽ idᴰ)) (_ , fᴰ)
      ⋆IdRᴰⱽ = λ fᴰ → sym (reind-filler _ _) ∙ ⋆IdRᴰᴰ fᴰ

      ⋆IdRⱽᴰ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
        → Path (∫Hom[ _ , _ ]) (_ , (fⱽ ⋆ⱽᴰ idᴰ)) (_ , fⱽ)
      ⋆IdRⱽᴰ = λ fᴰ → sym (reind-filler _ _) ∙ ⋆IdRᴰᴰ fᴰ

      ⋆IdRⱽⱽ : ∀ {x xᴰ yᴰ}(fⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
        → Path (∫Hom[ _ , _ ]) (_ , (fⱽ ⋆ⱽ idᴰ)) (_ , fⱽ)
      ⋆IdRⱽⱽ fⱽ = ⋆IdRⱽᴰ fⱽ

      ⋆Assocⱽᴰᴰ : ∀ {x y z wᴰ xᴰ yᴰ zᴰ}
        {g : C.Hom[ x , y ]}
        {h : C.Hom[ y , z ]}
        (fⱽ : Hom[ C.id {x} ][ wᴰ , xᴰ ])
        (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
        (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰ hᴰ)
            (_ , fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰ hᴰ))
      ⋆Assocⱽᴰᴰ _ _ _ = ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ reind-filler _ _

      ⋆Assocᴰⱽᴰ : ∀ {w x z wᴰ xᴰ yᴰ zᴰ}
        {f : C.Hom[ w , x ]}
        {h : C.Hom[ x , z ]}
        (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
        (gⱽ : Hom[ C.id {x} ][ xᴰ , yᴰ ])
        (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰ hᴰ)
            (_ , fᴰ ⋆ᴰ (gⱽ ⋆ⱽᴰ hᴰ))
      ⋆Assocᴰⱽᴰ fᴰ gⱽ hᴰ = ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩

      ⋆Assocᴰᴰⱽ : ∀ {w x y wᴰ xᴰ yᴰ zᴰ}
        {f : C.Hom[ w , x ]}
        {g : C.Hom[ x , y ]}
        (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
        (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
        (hⱽ : Hom[ C.id ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fᴰ ⋆ᴰ gᴰ) ⋆ᴰⱽ hⱽ)
            (_ , fᴰ ⋆ᴰ (gᴰ ⋆ᴰⱽ hⱽ))
      ⋆Assocᴰᴰⱽ fᴰ gᴰ hⱽ = (sym $ reind-filler _ _) ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩

      ⋆Assocⱽⱽᴰ : ∀ {y z wᴰ xᴰ yᴰ zᴰ}
        {h : C.Hom[ y , z ]}
        (fⱽ : Hom[ C.id ][ wᴰ , xᴰ ])
        (gⱽ : Hom[ C.id ][ xᴰ , yᴰ ])
        (hᴰ : Hom[ h ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fⱽ ⋆ⱽ gⱽ) ⋆ⱽᴰ hᴰ)
            (_ , fⱽ ⋆ⱽᴰ (gⱽ ⋆ⱽᴰ hᴰ))
      ⋆Assocⱽⱽᴰ fⱽ gⱽ hᴰ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

      ⋆Assocⱽᴰⱽ : ∀ {x y wᴰ xᴰ yᴰ zᴰ}
        {g : C.Hom[ x , y ]}
        (fⱽ : Hom[ C.id ][ wᴰ , xᴰ ])
        (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
        (hⱽ : Hom[ C.id ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fⱽ ⋆ⱽᴰ gᴰ) ⋆ᴰⱽ hⱽ)
            (_ , fⱽ ⋆ⱽᴰ (gᴰ ⋆ᴰⱽ hⱽ))
      ⋆Assocⱽᴰⱽ fⱽ gᴰ hⱽ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

      ⋆Assocᴰⱽⱽ : ∀ {w x wᴰ xᴰ yᴰ zᴰ}
        {f : C.Hom[ w , x ]}
        (fᴰ : Hom[ f ][ wᴰ , xᴰ ])
        (gⱽ : Hom[ C.id ][ xᴰ , yᴰ ])
        (hⱽ : Hom[ C.id ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fᴰ ⋆ᴰⱽ gⱽ) ⋆ᴰⱽ hⱽ)
            (_ , fᴰ ⋆ᴰⱽ (gⱽ ⋆ⱽ hⱽ))
      ⋆Assocᴰⱽⱽ fᴰ gⱽ hⱽ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

      ⋆Assocⱽⱽⱽ : ∀ {x wᴰ xᴰ yᴰ zᴰ}
        (fⱽ : Hom[ C .id {x} ][ wᴰ , xᴰ ])
        (gⱽ : Hom[ C .id ][ xᴰ , yᴰ ])
        (hⱽ : Hom[ C .id ][ yᴰ , zᴰ ])
        → Path ∫Hom[ _ , _ ]
            (_ , (fⱽ ⋆ⱽ gⱽ) ⋆ⱽ hⱽ)
            (_ , fⱽ ⋆ⱽ (gⱽ ⋆ⱽ hⱽ))
      ⋆Assocⱽⱽⱽ fⱽ gⱽ hⱽ = (sym $ reind-filler _ _) ∙ ∫C.⟨ sym $ reind-filler _ _ ⟩⋆⟨⟩ ∙ ⋆Assocᴰᴰᴰ _ _ _ ∙ ∫C.⟨⟩⋆⟨ reind-filler _ _ ⟩ ∙ reind-filler _ _

    v[_] : (x : ob) → LocallySmallCategory ob[ x ]
    v[ x ] .Hom-ℓ = _
    v[ x ] .Hom[_,_] = Hom[ C.id ][_,_]
    v[ x ] .id = idᴰ
    v[ x ] ._⋆_ fⱽ gⱽ = fⱽ ⋆ⱽ gⱽ
    v[ x ] .⋆IdL fⱽ = rectify $ ≡out $ ⋆IdLⱽⱽ _
    v[ x ] .⋆IdR fⱽ = rectify $ ≡out $ ⋆IdRⱽⱽ _
    v[ x ] .⋆Assoc fⱽ gⱽ hⱽ = rectify $ ≡out $ ⋆Assocⱽⱽⱽ _ _ _
    v[ x ] .isSetHom = isSetHomᴰ

    module Cⱽ {x : ob} = LocallySmallCategory (v[ x ])
    open ∫C public

module _ {ob}{C : LocallySmallCategory ob}{obᴰ}(Cᴰ : LocallySmallCategoryᴰ C obᴰ) where
  private
    module C = LocallySmallCategory C
    module Cᴰ = LocallySmallCategoryᴰ Cᴰ
  module _ {obᴰᴰ}(Cᴰᴰ : LocallySmallCategoryᴰ Cᴰ.∫C obᴰᴰ) where
    private
      module Cᴰᴰ = LocallySmallCategoryᴰ Cᴰᴰ
    ∫Cᴰ : LocallySmallCategoryᴰ C λ x → Σω[ xᴰ ∈ obᴰ x ] obᴰᴰ (x , xᴰ)
    ∫Cᴰ .LocallySmallCategoryᴰ.Hom-ℓᴰ x xᴰ y yᴰ =
    -- This is inferrable but I've included it for the curious
      ℓ-max (Cᴰ.Hom-ℓᴰ x (xᴰ .fst) y (yᴰ .fst))
            (Cᴰᴰ.Hom-ℓᴰ (x , xᴰ .fst) (xᴰ .snd) (y , yᴰ .fst) (yᴰ .snd))
    ∫Cᴰ .LocallySmallCategoryᴰ.Hom[_][_,_] f xᴰxᴰᴰ yᴰyᴰᴰ =
      Σ[ fᴰ ∈ Cᴰ.Hom[ f ][ xᴰxᴰᴰ .fst , yᴰyᴰᴰ .fst ] ]
        Cᴰᴰ.Hom[ f , fᴰ ][ xᴰxᴰᴰ .snd , yᴰyᴰᴰ .snd ]
    ∫Cᴰ .LocallySmallCategoryᴰ.idᴰ = Cᴰ.idᴰ , Cᴰᴰ.idᴰ
    ∫Cᴰ .LocallySmallCategoryᴰ._⋆ᴰ_ ffᴰ ggᴰ = (ffᴰ .fst Cᴰ.⋆ᴰ ggᴰ .fst) , (ffᴰ .snd Cᴰᴰ.⋆ᴰ ggᴰ .snd)
    ∫Cᴰ .LocallySmallCategoryᴰ.⋆IdLᴰ ffᴰ = ΣPathP (_ , Cᴰᴰ.⋆IdLᴰ (ffᴰ .snd))
    ∫Cᴰ .LocallySmallCategoryᴰ.⋆IdRᴰ ffᴰ = ΣPathP (_ , Cᴰᴰ.⋆IdRᴰ (ffᴰ .snd))
    ∫Cᴰ .LocallySmallCategoryᴰ.⋆Assocᴰ ffᴰ ggᴰ hhᴰ = ΣPathP (_ , Cᴰᴰ.⋆Assocᴰ (ffᴰ .snd) (ggᴰ .snd) (hhᴰ .snd))
    ∫Cᴰ .LocallySmallCategoryᴰ.isSetHomᴰ = isSetΣ Cᴰ.isSetHomᴰ (λ _ → Cᴰᴰ.isSetHomᴰ)

SET : LocallySmallCategoryᴰ LEVELω (mapω' hSet)
SET .LocallySmallCategoryᴰ.Hom-ℓᴰ = _
SET .LocallySmallCategoryᴰ.Hom[_][_,_] _ (liftω X) (liftω Y) = ⟨ X ⟩ → ⟨ Y ⟩
SET .LocallySmallCategoryᴰ.idᴰ = λ x → x
SET .LocallySmallCategoryᴰ._⋆ᴰ_ = λ f g x → g (f x)
SET .LocallySmallCategoryᴰ.⋆IdLᴰ = λ _ → refl
SET .LocallySmallCategoryᴰ.⋆IdRᴰ = λ _ → refl
SET .LocallySmallCategoryᴰ.⋆Assocᴰ = λ _ _ _ → refl
SET .LocallySmallCategoryᴰ.isSetHomᴰ {yᴰ = Y} = isSet→ (Y .lowerω .snd)

-- The total category LocallySmallCategoryᴰ.∫C SET is the "large category of all small sets"
-- Then
SETᴰ : LocallySmallCategoryᴰ
         (LEVEL ⊘ LocallySmallCategoryᴰ.∫C SET)
         (λ (ℓᴰ , (_ , liftω X)) → Liftω (⟨ X ⟩ → hSet ℓᴰ))
SETᴰ .LocallySmallCategoryᴰ.Hom-ℓᴰ = _
SETᴰ .LocallySmallCategoryᴰ.Hom[_][_,_] (_ , _ , f) (liftω Xᴰ) (liftω Yᴰ) =
  ∀ x → ⟨ Xᴰ x ⟩ → ⟨ Yᴰ (f x ) ⟩
SETᴰ .LocallySmallCategoryᴰ.idᴰ = λ x xᴰ → xᴰ
SETᴰ .LocallySmallCategoryᴰ._⋆ᴰ_ {f = (_ , _ , f)} fᴰ gᴰ x xᴰ =
  gᴰ (f x) (fᴰ x xᴰ)
SETᴰ .LocallySmallCategoryᴰ.⋆IdLᴰ = λ _ → refl
SETᴰ .LocallySmallCategoryᴰ.⋆IdRᴰ = λ _ → refl
SETᴰ .LocallySmallCategoryᴰ.⋆Assocᴰ = λ _ _ _ → refl
SETᴰ .LocallySmallCategoryᴰ.isSetHomᴰ {yᴰ = liftω Yᴰ} =
  isSetΠ λ _ → isSet→ (Yᴰ _ .snd)

-- TODO:
--   should be able to rewrite this as LocallySmallNatTransᴰ
PRESHEAF : ∀ (C : Category ℓC ℓC')
  → LocallySmallCategoryᴰ LEVELω (mapω' (Presheaf C))
PRESHEAF C .LocallySmallCategoryᴰ.Hom-ℓᴰ = _
PRESHEAF C .LocallySmallCategoryᴰ.Hom[_][_,_] _ (liftω P) (liftω Q) = PshHom P Q
PRESHEAF C .LocallySmallCategoryᴰ.idᴰ = idPshHom
PRESHEAF C .LocallySmallCategoryᴰ._⋆ᴰ_  = _⋆PshHom_
PRESHEAF C .LocallySmallCategoryᴰ.⋆IdLᴰ = ⋆PshHomIdL
PRESHEAF C .LocallySmallCategoryᴰ.⋆IdRᴰ = ⋆PshHomIdR
PRESHEAF C .LocallySmallCategoryᴰ.⋆Assocᴰ = ⋆PshHomAssoc
PRESHEAF C .LocallySmallCategoryᴰ.isSetHomᴰ = isSetPshHom _ _

PRESHEAFᴰ : ∀ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → LocallySmallCategoryᴰ
      (LEVEL ⊘ LocallySmallCategoryᴰ.∫C (PRESHEAF C))
      λ (ℓPᴰ , (_ , liftω P)) → Liftω (Presheafᴰ P Cᴰ ℓPᴰ)
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.Hom-ℓᴰ = _
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.Hom[_][_,_] (_ , _ , α) (liftω Pᴰ) (liftω Qᴰ) =
  PshHomᴰ α Pᴰ Qᴰ
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.idᴰ = idPshHomᴰ
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ._⋆ᴰ_ = _⋆PshHomᴰ_
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.⋆IdLᴰ {yᴰ = liftω Qᴰ} αᴰ =
  makePshHomᴰPathP _ _ _ (funExt λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl)
  where module Qᴰ = PresheafᴰNotation Qᴰ
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.⋆IdRᴰ {yᴰ = liftω Qᴰ} αᴰ =
  makePshHomᴰPathP _ _ _ (funExt λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl)
  where module Qᴰ = PresheafᴰNotation Qᴰ
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.⋆Assocᴰ {wᴰ = liftω Qᴰ} αᴰ βᴰ γᴰ =
  makePshHomᴰPathP _ _ _ (funExt λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl)
  where module Qᴰ = PresheafᴰNotation Qᴰ
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.isSetHomᴰ = isSetPshHomᴰ _ _ _
