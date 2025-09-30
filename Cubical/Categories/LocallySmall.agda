module Cubical.Categories.LocallySmall where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

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

-- A LocallySmallCategory has a "proper class" of objects, but small hom sets
record LocallySmallCategory (ob : Typeω): Typeω where
  field
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

    ∫C : LocallySmallCategory (Σω[ x ∈ ob ] ob[ x ])
    ∫C .LocallySmallCategory.Hom-ℓ = _
    ∫C .LocallySmallCategory.Hom[_,_] xxᴰ yyᴰ =
      Σ[ f ∈ C.Hom[ xxᴰ .fst , yyᴰ .fst ] ]
      Hom[ f ][ xxᴰ .snd , yyᴰ .snd ]
    ∫C .LocallySmallCategory.id = C.id , idᴰ
    ∫C .LocallySmallCategory._⋆_ ffᴰ ggᴰ = (ffᴰ .fst C.⋆ ggᴰ .fst) , (ffᴰ .snd ⋆ᴰ ggᴰ .snd)
    ∫C .LocallySmallCategory.⋆IdL ffᴰ = ΣPathP (C.⋆IdL (ffᴰ .fst) , ⋆IdLᴰ (ffᴰ .snd))
    ∫C .LocallySmallCategory.⋆IdR ffᴰ = ΣPathP (C.⋆IdR (ffᴰ .fst) , ⋆IdRᴰ (ffᴰ .snd))
    ∫C .LocallySmallCategory.⋆Assoc ffᴰ ggᴰ hhᴰ = ΣPathP ((C.⋆Assoc _ _ _) , (⋆Assocᴰ _ _ _))
    ∫C .LocallySmallCategory.isSetHom = isSetΣ C.isSetHom (λ _ → isSetHomᴰ)

    open LocallySmallCategory ∫C public
-- module _ {ob}(C : LocallySmallCategory ob) where
--   private
--     module C = LocallySmallCategory C
--   record BundledCategoryᴰ : Typeω where
--     field
--       ob-ℓ : ob → Level
--       ob[_] : ∀ (x : ob) → Type (ob-ℓ x)
--       Hom-ℓᴰ : ob → ob → Level
--       Hom[_][_,_] : ∀ {x y}(f : C.Hom[ x , y ])(xᴰ : ob[ x ])(yᴰ : ob[ y ]) → Type (Hom-ℓᴰ x y)
--       idᴰ : ∀ {x} {p : ob[ x ]} → Hom[ C.id ][ p , p ]
--       _⋆ᴰ_ : ∀ {x y z} {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]} {xᴰ yᴰ zᴰ}
--         → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ] → Hom[ f C.⋆ g ][ xᴰ , zᴰ ]

--     infixr 9 _⋆ᴰ_

--     _≡[_]_ : ∀ {x y xᴰ yᴰ} {f g : C.Hom[ x , y ]}
--       → (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (p : f ≡ g) (gᴰ : Hom[ g ][ xᴰ , yᴰ ])
--       → Type (Hom-ℓᴰ x y)
--     _≡[_]_ {x} {y} {xᴰ} {yᴰ} fᴰ p gᴰ = PathP (λ i → Hom[ p i ][ xᴰ , yᴰ ]) fᴰ gᴰ

--     infix 2 _≡[_]_

--     field
--       ⋆IdLᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → idᴰ ⋆ᴰ fᴰ ≡[ C.⋆IdL f ] fᴰ
--       ⋆IdRᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) → fᴰ ⋆ᴰ idᴰ ≡[ C.⋆IdR f ] fᴰ
--       ⋆Assocᴰ : ∀ {x y z w} {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]}  {h : C.Hom[ z , w ]} {xᴰ yᴰ zᴰ wᴰ}
--         (fᴰ : Hom[ f ][ xᴰ , yᴰ ]) (gᴰ : Hom[ g ][ yᴰ , zᴰ ]) (hᴰ : Hom[ h ][ zᴰ , wᴰ ])
--         → (fᴰ ⋆ᴰ gᴰ) ⋆ᴰ hᴰ ≡[ C.⋆Assoc f g h ] fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ)
--       isSetHomᴰ : ∀ {x y} {f : C.Hom[ x , y ]} {xᴰ yᴰ} → isSet Hom[ f ][ xᴰ , yᴰ ]

--     ∫C : LocallySmallCategory (Σω[ x ∈ ob ] ob[ x ])
--     ∫C .LocallySmallCategory.Hom-ℓ = _
--     ∫C .LocallySmallCategory.Hom[_,_] xxᴰ yyᴰ =
--       Σ[ f ∈ C.Hom[ xxᴰ .fst , yyᴰ .fst ] ]
--       Hom[ f ][ xxᴰ .snd , yyᴰ .snd ]
--     ∫C .LocallySmallCategory.id = C.id , idᴰ
--     ∫C .LocallySmallCategory._⋆_ ffᴰ ggᴰ = (ffᴰ .fst C.⋆ ggᴰ .fst) , (ffᴰ .snd ⋆ᴰ ggᴰ .snd)
--     ∫C .LocallySmallCategory.⋆IdL ffᴰ = ΣPathP (C.⋆IdL (ffᴰ .fst) , ⋆IdLᴰ (ffᴰ .snd))
--     ∫C .LocallySmallCategory.⋆IdR ffᴰ = ΣPathP (C.⋆IdR (ffᴰ .fst) , ⋆IdRᴰ (ffᴰ .snd))
--     ∫C .LocallySmallCategory.⋆Assoc ffᴰ ggᴰ hhᴰ = ΣPathP ((C.⋆Assoc _ _ _) , (⋆Assocᴰ _ _ _))
--     ∫C .LocallySmallCategory.isSetHom = isSetΣ C.isSetHom (λ _ → isSetHomᴰ)

--     open LocallySmallCategory ∫C public

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
    ∫Cᴰ .LocallySmallCategoryᴰ.⋆IdLᴰ ffᴰ = ΣPathP ((Cᴰ.⋆IdLᴰ (ffᴰ .fst)) , (Cᴰᴰ.⋆IdLᴰ (ffᴰ .snd)))
    ∫Cᴰ .LocallySmallCategoryᴰ.⋆IdRᴰ ffᴰ = ΣPathP ((Cᴰ.⋆IdRᴰ (ffᴰ .fst)) , (Cᴰᴰ.⋆IdRᴰ (ffᴰ .snd)))
    ∫Cᴰ .LocallySmallCategoryᴰ.⋆Assocᴰ ffᴰ ggᴰ hhᴰ = ΣPathP ((Cᴰ.⋆Assocᴰ (ffᴰ .fst) (ggᴰ .fst) (hhᴰ .fst)) , (Cᴰᴰ.⋆Assocᴰ (ffᴰ .snd) (ggᴰ .snd) (hhᴰ .snd)))
    ∫Cᴰ .LocallySmallCategoryᴰ.isSetHomᴰ = isSetΣ Cᴰ.isSetHomᴰ (λ _ → Cᴰᴰ.isSetHomᴰ)

PRESHEAF : ∀ (C : Category ℓC ℓC') → LocallySmallCategoryᴰ (CategoriesAreLocallySmall LEVEL) λ { (liftω ℓ) → Liftω (Presheaf C ℓ) }
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
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.⋆IdLᴰ {yᴰ = liftω Qᴰ} αᴰ = makePshHomᴰPathP _ _ _ (funExt λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl)
  where module Qᴰ = PresheafᴰNotation Qᴰ
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.⋆IdRᴰ {yᴰ = liftω Qᴰ} αᴰ = makePshHomᴰPathP _ _ _ (funExt λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl)
  where module Qᴰ = PresheafᴰNotation Qᴰ
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.⋆Assocᴰ {wᴰ = liftω Qᴰ} αᴰ βᴰ γᴰ = makePshHomᴰPathP _ _ _ (funExt λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl)
  where module Qᴰ = PresheafᴰNotation Qᴰ
PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.isSetHomᴰ = isSetPshHomᴰ _ _ _
