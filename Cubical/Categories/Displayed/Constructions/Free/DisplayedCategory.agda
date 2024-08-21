{-
  The free displayed category
-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Free.DisplayedCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Constructions.TotalCategory
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓCᴰᴰ ℓCᴰᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
module FreeDisplayedCategory
  (C : Category ℓC ℓC')
  (Ob : C .ob → Type ℓCᴰ)
  (GHom : ∀ {x}{y} (f : C [ x , y ]) → Type ℓCᴰ')
  (GHomDom : ∀ {x}{y} {f : C [ x , y ]} → GHom f → Ob x)
  (GHomCod : ∀ {x}{y} {f : C [ x , y ]} → GHom f → Ob y)
  where
    data Homₑ : ∀ {x y} (f : C [ x , y ]) → Ob x → Ob y → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
    -- if we added a vertical hom we can avoid some PathPs, not sure if we care tho
    _≡[_]ₑ_ : ∀ {x y} {xᴰ yᴰ} {f f' : C [ x , y ]}
      → Homₑ f xᴰ yᴰ
      → f ≡ f'
      → Homₑ f' xᴰ yᴰ
      → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
    _≡[_]ₑ_ {xᴰ = xᴰ}{yᴰ} fᴰ p fᴰ' = PathP (λ i → Homₑ (p i) xᴰ yᴰ) fᴰ fᴰ'
    data Homₑ where
      iHom : ∀ {x y} {f : C [ x , y ]} → (fᴰ : GHom f)
        → Homₑ f (GHomDom fᴰ) (GHomCod fᴰ)
      idᴰₑ : ∀ {x} {xᴰ} → Homₑ (C .id {x}) xᴰ xᴰ
      _⋆ᴰₑ_ : ∀ {x y z} {xᴰ yᴰ zᴰ} {f : C [ x , y ]}{g : C [ y , z ]}
        → Homₑ f xᴰ yᴰ
        → Homₑ g yᴰ zᴰ
        → Homₑ (f ⋆⟨ C ⟩ g) xᴰ zᴰ
      ⋆IdLᴰₑ : ∀ {x y} {xᴰ yᴰ} {f : C [ x , y ]}
        → (fᴰ : Homₑ f xᴰ yᴰ)
        → (idᴰₑ ⋆ᴰₑ fᴰ) ≡[ C .⋆IdL f ]ₑ fᴰ
      ⋆IdRᴰₑ : ∀ {x y} {xᴰ yᴰ} {f : C [ x , y ]}
        → (fᴰ : Homₑ f xᴰ yᴰ)
        → (fᴰ ⋆ᴰₑ idᴰₑ) ≡[ C .⋆IdR f ]ₑ fᴰ
      ⋆Assocᴰₑ : ∀ {w x y z} {wᴰ xᴰ yᴰ zᴰ}
        {f : C [ w , x ]}{g : C [ x , y ]}{h : C [ y , z ]}
        (fᴰ : Homₑ f wᴰ xᴰ)
        (gᴰ : Homₑ g xᴰ yᴰ)
        (hᴰ : Homₑ h yᴰ zᴰ)
        → ((fᴰ ⋆ᴰₑ gᴰ) ⋆ᴰₑ hᴰ) ≡[ C .⋆Assoc f g h ]ₑ (fᴰ ⋆ᴰₑ (gᴰ ⋆ᴰₑ hᴰ))
      isSetHomᴰₑ : ∀ {x y}{xᴰ yᴰ}{f : C [ x , y ]} → isSet (Homₑ f xᴰ yᴰ)

    open Categoryᴰ
    FreeDispCat : Categoryᴰ C ℓCᴰ (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
    FreeDispCat .ob[_] = Ob
    FreeDispCat .Hom[_][_,_] = Homₑ
    FreeDispCat .idᴰ = idᴰₑ
    FreeDispCat ._⋆ᴰ_ = _⋆ᴰₑ_
    FreeDispCat .⋆IdLᴰ = ⋆IdLᴰₑ
    FreeDispCat .⋆IdRᴰ = ⋆IdRᴰₑ
    FreeDispCat .⋆Assocᴰ = ⋆Assocᴰₑ
    FreeDispCat .isSetHomᴰ = isSetHomᴰₑ

    -- recursion principle:
    module _ (Cᴰ : Categoryᴰ C ℓCᴰᴰ ℓCᴰᴰ')
      where
      private
        module Cᴰ = Categoryᴰ Cᴰ
      module _
        (rec-F-obᴰ : ∀ {x} → Ob x → Cᴰ.ob[ x ])
        (rec-F-homᴰ-gen : ∀ {x y} {f : C [ x , y ]} → (g : GHom f)
           → Cᴰ.Hom[ f ][ rec-F-obᴰ (GHomDom g) , rec-F-obᴰ (GHomCod g) ])
        where
        rec-F-homᴰ : ∀ {x y}{xᴰ yᴰ} {f : C [ x , y ]}
           → Homₑ f xᴰ yᴰ
           → Cᴰ.Hom[ f ][ rec-F-obᴰ xᴰ , rec-F-obᴰ yᴰ ]
        rec-F-homᴰ (iHom fᴰ) = rec-F-homᴰ-gen fᴰ
        rec-F-homᴰ idᴰₑ = Cᴰ.idᴰ
        rec-F-homᴰ (fᴰ ⋆ᴰₑ gᴰ) = rec-F-homᴰ fᴰ Cᴰ.⋆ᴰ rec-F-homᴰ gᴰ
        rec-F-homᴰ (⋆IdLᴰₑ fᴰ i) = Cᴰ.⋆IdLᴰ (rec-F-homᴰ fᴰ) i
        rec-F-homᴰ (⋆IdRᴰₑ fᴰ i) = Cᴰ.⋆IdRᴰ (rec-F-homᴰ fᴰ) i
        rec-F-homᴰ (⋆Assocᴰₑ fᴰ gᴰ hᴰ i) =
          Cᴰ.⋆Assocᴰ (rec-F-homᴰ fᴰ) (rec-F-homᴰ gᴰ) (rec-F-homᴰ hᴰ) i
        rec-F-homᴰ (isSetHomᴰₑ fᴰ gᴰ p q i j) =
          Cᴰ.isSetHomᴰ (rec-F-homᴰ fᴰ) (rec-F-homᴰ gᴰ)
          (cong rec-F-homᴰ p) (cong rec-F-homᴰ q)
          i j

        rec : Functorᴰ Id FreeDispCat Cᴰ
        rec .Functorᴰ.F-obᴰ = rec-F-obᴰ
        rec .Functorᴰ.F-homᴰ = rec-F-homᴰ
        rec .Functorᴰ.F-idᴰ = refl
        rec .Functorᴰ.F-seqᴰ _ _ = refl
    -- elimination principle
    module _ (Cᴰᴰ : Categoryᴰ (∫C {C = C} FreeDispCat) ℓCᴰᴰ ℓCᴰᴰ')
      where
      private
        module Cᴰᴰ = Categoryᴰ Cᴰᴰ
        module FDC = Categoryᴰ FreeDispCat
      module _
        (elim-F-obᴰ : ∀ x xᴰ → Cᴰᴰ.ob[ x , xᴰ ])
        (elim-F-homᴰ-gen : ∀ {x y} {f : C [ x , y ]} → (g : GHom f)
           → Cᴰᴰ.Hom[ f , iHom g ][ elim-F-obᴰ x (GHomDom g) , elim-F-obᴰ y (GHomCod g) ])
        where
        -- elim-F-homᴰ : ∀ {x y f xᴰ yᴰ} (fᴰ : FDC.Hom[ f ][ xᴰ , yᴰ ])
        --     → Cᴰᴰ.Hom[ f , fᴰ ][ elim-F-obᴰ x xᴰ , elim-F-obᴰ y yᴰ ]
        -- elim-F-homᴰ (iHom fᴰ) = elim-F-homᴰ-gen fᴰ
        -- elim-F-homᴰ idᴰₑ = Cᴰᴰ.idᴰ
        -- elim-F-homᴰ (fᴰ ⋆ᴰₑ gᴰ) = elim-F-homᴰ fᴰ Cᴰᴰ.⋆ᴰ elim-F-homᴰ gᴰ
        -- elim-F-homᴰ (⋆IdLᴰₑ fᴰ i) = Cᴰᴰ.⋆IdLᴰ (elim-F-homᴰ fᴰ) i
        -- elim-F-homᴰ (⋆IdRᴰₑ fᴰ i) = Cᴰᴰ.⋆IdRᴰ (elim-F-homᴰ fᴰ) i
        -- elim-F-homᴰ (⋆Assocᴰₑ fᴰ gᴰ hᴰ i) = Cᴰᴰ.⋆Assocᴰ (elim-F-homᴰ fᴰ) (elim-F-homᴰ gᴰ) (elim-F-homᴰ hᴰ) i
        -- elim-F-homᴰ (isSetHomᴰₑ fᴰ gᴰ p q i j) = isOfHLevel→isOfHLevelDep 2
        --   (λ _ → Cᴰᴰ.isSetHomᴰ)
        --   (elim-F-homᴰ fᴰ) (elim-F-homᴰ gᴰ)
        --   (λ i → elim-F-homᴰ (p i)) (λ i → elim-F-homᴰ (q i))
        --   (isSetHomᴰₑ fᴰ gᴰ p q) i j
        -- elim : GlobalSection Cᴰᴰ
        -- elim .Section.F-obᴰ xxᴰ = elim-F-obᴰ (xxᴰ .fst) (xxᴰ .snd)
        -- elim .Section.F-homᴰ ffᴰ = elim-F-homᴰ (ffᴰ .snd)
        -- elim .Section.F-idᴰ = refl
        -- elim .Section.F-seqᴰ (f , fᴰ) (g , gᴰ) = refl

        -- an alternate way to construct elim that generalizes to
        -- fibrations more easily
        elim' : GlobalSection Cᴰᴰ
        elim' = reindS {!!} (compSectionFunctor {!!} {!!})
