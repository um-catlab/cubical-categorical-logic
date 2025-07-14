{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Constructions.TotalCategory as TotalCat
import Cubical.Categories.Displayed.Reasoning as Reasoning
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Functor

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ : Level

open Category
open Functor
open Functorᴰ

-- equivalent to the data of a presheaf Pᴰ over ∫ D and a natural transformation
-- Pᴰ → P ∘ Fst
Presheafᴰ : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → (P : Presheaf C ℓP) → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-suc ℓP))
                    (ℓ-suc ℓPᴰ))
Presheafᴰ {ℓP = ℓP} D P ℓPᴰ = Functorᴰ P (D ^opᴰ) (SETᴰ ℓP ℓPᴰ)

PRESHEAFᴰ : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → ∀ (ℓP ℓPᴰ : Level) → Categoryᴰ (PresheafCategory C ℓP) _ _
PRESHEAFᴰ Cᴰ ℓP ℓPᴰ = FUNCTORᴰ (Cᴰ ^opᴰ) (SETᴰ ℓP ℓPᴰ)

-- TODO: make a PresheafNotation to match
module PresheafᴰNotation {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓD ℓD'}
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ Cᴰ P ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ

  pob[_] : C .ob → Type ℓP
  pob[ x ] = ⟨ P ⟅ x ⟆ ⟩

  p[_][_] : ∀ {x} → ⟨ P ⟅ x ⟆ ⟩ → Cᴰ.ob[ x ] → Type ℓPᴰ
  p[ f ][ xᴰ ] = ⟨ Pᴰ .F-obᴰ xᴰ f ⟩

  _≡[_]_ : ∀ {x xᴰ} {f g : ⟨ P ⟅ x ⟆ ⟩} → p[ f ][ xᴰ ] → f ≡ g → p[ g ][ xᴰ ]
    → Type ℓPᴰ
  _≡[_]_ {x} {xᴰ} {f} {g} fᴰ f≡g gᴰ = PathP (λ i → p[ f≡g i ][ xᴰ ]) fᴰ gᴰ

  _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{g}
    → Cᴰ [ f ][ xᴰ , yᴰ ] → p[ g ][ yᴰ ]
    → p[ g ∘ᴾ⟨ C , P ⟩ f ][ xᴰ ]
  fᴰ ⋆ᴰ gᴰ = Pᴰ .F-homᴰ fᴰ _ gᴰ

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ D P ℓPᴰ) where
  private
    module D = Categoryᴰ D
    module R = Reasoning D
    module Pᴰ = PresheafᴰNotation Pᴰ

  record UniversalElementᴰ (ue : UniversalElement C P)
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-max ℓP ℓPᴰ)) where
    open UniversalElementNotation ue
    open Categoryᴰ D
    field
      vertexᴰ : ob[ vertex ]
      elementᴰ : Pᴰ.p[ element ][ vertexᴰ ]
      universalᴰ : ∀ {x xᴰ} →
        isIsoOver (equivToIso (_ , (universal x)))
          Hom[_][ xᴰ , vertexᴰ ]
          (λ p → Pᴰ.p[ p ][ xᴰ ])
          λ f fᴰ → fᴰ Pᴰ.⋆ᴰ elementᴰ
    open isIsoOver

  module _ where
    open UniversalElement
    open UniversalElementᴰ
    ∫UE : ∀ {ue : UniversalElement C P} (ueᴰ : UniversalElementᴰ ue)
      → UniversalElement (TotalCat.∫C D) (ΣF ∘F TotalCat.∫F Pᴰ)
    ∫UE {ue = ue} ueᴰ .vertex = ue .vertex , ueᴰ .vertexᴰ
    ∫UE {ue = ue} ueᴰ .element = ue .element , ueᴰ .elementᴰ
    ∫UE {ue = ue} ueᴰ .universal (v , vᴰ) =
      isIsoToIsEquiv (isIsoOver→isIsoΣ (ueᴰ .universalᴰ))

  module UniversalElementᴰNotation
    {ue : UniversalElement C P}
    (ueᴰ : UniversalElementᴰ ue)
    where
    open UniversalElementNotation ue public
    open UniversalElementᴰ ueᴰ public
    private
      module ∫ue = UniversalElementNotation (∫UE ueᴰ)

    introᴰ : ∀ {x xᴰ} (p : ⟨ P ⟅ x ⟆ ⟩)
        → Pᴰ.p[ p ][ xᴰ ]
        → D [ intro p ][ xᴰ , vertexᴰ ]
    introᴰ p pᴰ = ∫ue.intro (p , pᴰ) .snd

    βᴰ : ∀ {x xᴰ} {p : Pᴰ.pob[ x ] } {pᴰ : Pᴰ.p[ p ][ xᴰ ]}
         → (introᴰ p pᴰ Pᴰ.⋆ᴰ elementᴰ) Pᴰ.≡[ β ] pᴰ
    βᴰ = cong snd ∫ue.β

    ηᴰ : ∀ {x xᴰ} {f : C [ x , vertex ]} {fᴰ : D [ f ][ xᴰ , vertexᴰ ]}
         → fᴰ D.≡[ η {f = f} ] (introᴰ _ (F-homᴰ Pᴰ fᴰ element elementᴰ))
    ηᴰ = R.rectify $ cong snd ∫ue.η

    weak-ηᴰ : D.idᴰ D.≡[ weak-η ] introᴰ _ elementᴰ
    weak-ηᴰ = R.rectify $ cong snd ∫ue.weak-η

    extensionalityᴰ
      : ∀ {x xᴰ} {f g : C [ x , vertex ]}
        {fᴰ : D [ f ][ xᴰ , vertexᴰ ]}
        {gᴰ : D [ g ][ xᴰ , vertexᴰ ]}
      → (fπ≡gπ : element ∘ᴾ⟨ C , P ⟩ f ≡ element ∘ᴾ⟨ C , P ⟩ g)
      → (fᴰ Pᴰ.⋆ᴰ elementᴰ) Pᴰ.≡[ fπ≡gπ ] (gᴰ Pᴰ.⋆ᴰ elementᴰ)
      → fᴰ D.≡[ extensionality fπ≡gπ ] gᴰ
    extensionalityᴰ fπ≡gπ p = R.rectify $
      cong snd (∫ue.extensionality (ΣPathP (fπ≡gπ , p)))

-- A vertical presheaf is a displayed presheaf over a representable
Presheafⱽ : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → (c : C .ob) → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-suc ℓC')) ℓD) ℓD')
                        (ℓ-suc ℓPᴰ))
Presheafⱽ D c = Presheafᴰ D (YO ⟅ c ⟆)

actⱽ : {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
          → {x : C .ob} → {ℓP : Level}
  → (Pⱽ : Presheafⱽ Cᴰ x ℓP)
  → ∀ {y}{yᴰ xᴰ} {f : C [ y , x ]}
  → Cᴰ [ f ][ yᴰ , xᴰ ]
  → ⟨ Pⱽ .F-obᴰ xᴰ (C .id) ⟩
  → ⟨ Pⱽ .F-obᴰ yᴰ f ⟩
actⱽ {C = C} Pⱽ fᴰ pⱽ =
  subst (λ f → ⟨ Pⱽ .F-obᴰ _ f ⟩) (C .⋆IdR _) (Pⱽ .F-homᴰ  fᴰ _ pⱽ)

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
         (x : C .ob) (Pᴰ : Presheafⱽ D x ℓPᴰ) where
  record UniversalElementⱽ
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') ℓPᴰ) where
    open Categoryᴰ D
    field
      vertexⱽ : ob[ x ]
      elementⱽ : ⟨ Pᴰ .F-obᴰ vertexⱽ (C .id) ⟩
      universalⱽ : ∀ {y yᴰ}{f : C [ y , x ]} →
        isIso λ (fᴰ : D [ f ][ yᴰ , vertexⱽ ]) → actⱽ Pᴰ fᴰ elementⱽ

    introⱽ : ∀ {y yᴰ} (f : C [ y , x ])
      → ⟨ Pᴰ .F-obᴰ yᴰ f ⟩
      → D [ f ][ yᴰ , vertexⱽ ]
    introⱽ f = universalⱽ .fst

    βⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {pᴰ : ⟨ Pᴰ .F-obᴰ yᴰ f ⟩}
      → actⱽ Pᴰ (introⱽ f pᴰ) elementⱽ ≡ pᴰ
    βⱽ = universalⱽ .snd .fst _

    ηⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {fᴰ : D [ f ][ yᴰ , vertexⱽ ]}
      → fᴰ ≡ introⱽ f (actⱽ Pᴰ fᴰ elementⱽ)
    ηⱽ = sym (universalⱽ .snd .snd _)
