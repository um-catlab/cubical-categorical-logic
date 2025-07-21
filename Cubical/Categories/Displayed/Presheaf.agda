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
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Instances.Functor

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ : Level

open Functor
open Functorᴰ

-- equivalent to the data of a presheaf Pᴰ over ∫ D and a natural transformation
-- Pᴰ → P ∘ Fst
--
-- IMO the order of D and P here should be swapped to match Functorᴰ
Presheafᴰ : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → (P : Presheaf C ℓP) → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-suc ℓP))
                    (ℓ-suc ℓPᴰ))
Presheafᴰ {ℓP = ℓP} D P ℓPᴰ = Functorᴰ P (D ^opᴰ) (SETᴰ ℓP ℓPᴰ)

PRESHEAFᴰ : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → ∀ (ℓP ℓPᴰ : Level) → Categoryᴰ (PresheafCategory C ℓP) _ _
PRESHEAFᴰ Cᴰ ℓP ℓPᴰ = FUNCTORᴰ (Cᴰ ^opᴰ) (SETᴰ ℓP ℓPᴰ)

∫P : {C : Category ℓC ℓC'} {D : Categoryᴰ C ℓD ℓD'}
     → {P : Presheaf C ℓP} → {ℓPᴰ : Level}
     → Presheafᴰ D P ℓPᴰ
     → Presheaf (TotalCat.∫C D) (ℓ-max ℓP ℓPᴰ)
∫P Pᴰ = ΣF ∘F TotalCat.∫F Pᴰ

module PresheafᴰNotation {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓD ℓD'}
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ Cᴰ P ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
  infixr 9 _⋆ᴰ_
  infix 2 _≡[_]_

  pob[_] : C.ob → Type ℓP
  pob[ x ] = ⟨ P ⟅ x ⟆ ⟩

  p[_][_] : ∀ {x} → P.p[ x ] → Cᴰ.ob[ x ] → Type ℓPᴰ
  p[ f ][ xᴰ ] = ⟨ Pᴰ .F-obᴰ xᴰ f ⟩

  _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{g}
     → Cᴰ [ f ][ xᴰ , yᴰ ] → p[ g ][ yᴰ ]
     → p[ f P.⋆ g ][ xᴰ ]
  fᴰ ⋆ᴰ gᴰ = Pᴰ .F-homᴰ fᴰ _ gᴰ

  isSetPsh : ∀ {x} → isSet (P.p[ x ])
  isSetPsh {x} = (P ⟅ x ⟆) .snd

  _≡[_]_ : ∀ {x xᴰ} {f g : P.p[ x ]} → p[ f ][ xᴰ ] → f ≡ g → p[ g ][ xᴰ ]
    → Type ℓPᴰ
  _≡[_]_ {x} {xᴰ} {f} {g} fᴰ f≡g gᴰ =
    PathP (λ i → p[ f≡g i ][ xᴰ ]) fᴰ gᴰ

  reind : ∀ {x}{xᴰ}{f g : P.p[ x ]}(f≡g : f ≡ g)
      → p[ f ][ xᴰ ] → p[ g ][ xᴰ ]
  reind = subst p[_][ _ ]

  opaque
    reind-filler : ∀ {x}{xᴰ}{f g : P.p[ x ]}(f≡g : f ≡ g)
      → (fᴰ : p[ f ][ xᴰ ])
      → fᴰ ≡[ f≡g ] reind f≡g fᴰ
    reind-filler = subst-filler p[_][ _ ]

  ≡in : {a : C.ob} {f g : P.p[ a ]}
        {aᴰ : Cᴰ.ob[ a ]}
        {fᴰ : p[ f ][ aᴰ ]}
        {gᴰ : p[ g ][ aᴰ ]}
        {p : f ≡ g}
      → (fᴰ ≡[ p ] gᴰ)
      → (f , fᴰ) ≡ (g , gᴰ)
  ≡in e = ΣPathP (_ , e)

  ≡out : {a : C.ob} {f g : P.p[ a ]}
         {aᴰ : Cᴰ.ob[ a ]}
         {fᴰ : p[ f ][ aᴰ ]}
         {gᴰ : p[ g ][ aᴰ ]}
       → (e : (f , fᴰ) ≡ (g , gᴰ))
       → (fᴰ ≡[ fst (PathPΣ e) ] gᴰ)
  ≡out e = snd (PathPΣ e)

  rectify : {a : C.ob} {f g : P.p[ a ]} {p p' : f ≡ g}
      {aᴰ : Cᴰ.ob[ a ]}
      {fᴰ : p[ f ][ aᴰ ]}
      {gᴰ : p[ g ][ aᴰ ]}
    → fᴰ ≡[ p ] gᴰ → fᴰ ≡[ p' ] gᴰ
  rectify {fᴰ = fᴰ} {gᴰ = gᴰ} = subst (fᴰ ≡[_] gᴰ) (isSetPsh _ _ _ _)

  open PresheafNotation (∫P Pᴰ) public

  _⋆ⱽᴰ_ : ∀ {x xᴰ xᴰ'}{g}
     → Cᴰ [ C.id {x} ][ xᴰ , xᴰ' ] → p[ g ][ xᴰ' ]
     → p[ g ][ xᴰ ]
  fⱽ ⋆ⱽᴰ gᴰ = reind (P.⋆IdL _) (fⱽ ⋆ᴰ gᴰ)

  opaque
    ⋆ⱽIdL : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{g}
      → (gᴰ : p[ g ][ xᴰ ])
      → Cᴰ.idᴰ ⋆ⱽᴰ gᴰ ≡ gᴰ
    ⋆ⱽIdL gᴰ = rectify $ ≡out $ (sym $ ≡in $ reind-filler _ _) ∙ ⋆IdL _

    -- TODO: ⋆ⱽAssoc but it relies on the definition _⋆ⱽ_ in the fiber

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
      → UniversalElement (TotalCat.∫C D) (∫P Pᴰ)
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
    module ∫ue = UniversalElementNotation
        {C = TotalCat.∫C {C = C} D} (∫UE ueᴰ)
    private
      module P = PresheafNotation {C = C} P

    introᴰ : ∀ {x xᴰ} (p : ⟨ P ⟅ x ⟆ ⟩)
        → Pᴰ.p[ p ][ xᴰ ]
        → D [ intro p ][ xᴰ , vertexᴰ ]
    introᴰ p pᴰ = ∫ue.intro (p , pᴰ) .snd

    -- introᴰ⟨_⟩ : ∀ {x xᴰ} (p : ⟨ P ⟅ x ⟆ ⟩)
    --     → Pᴰ.p[ p ][ xᴰ ]
    --     → D [ intro p ][ xᴰ , vertexᴰ ]
    opaque
      unfolding β
      βᴰ : ∀ {x xᴰ} {p : Pᴰ.pob[ x ] } {pᴰ : Pᴰ.p[ p ][ xᴰ ]}
           → (introᴰ p pᴰ Pᴰ.⋆ᴰ elementᴰ) Pᴰ.≡[ β ] pᴰ
      βᴰ = cong snd ∫ue.β

      ηᴰ : ∀ {x xᴰ} {f : C [ x , vertex ]} {fᴰ : D [ f ][ xᴰ , vertexᴰ ]}
           → fᴰ D.≡[ η {f = f} ] (introᴰ _ (fᴰ Pᴰ.⋆ᴰ elementᴰ))
      ηᴰ = R.rectify $ cong snd ∫ue.η

      weak-ηᴰ : D.idᴰ D.≡[ weak-η ] introᴰ _ elementᴰ
      weak-ηᴰ = R.rectify $ cong snd ∫ue.weak-η

      extensionalityᴰ
        : ∀ {x xᴰ} {f g : C [ x , vertex ]}
          {fᴰ : D [ f ][ xᴰ , vertexᴰ ]}
          {gᴰ : D [ g ][ xᴰ , vertexᴰ ]}
        → (fπ≡gπ : f P.⋆ element  ≡ g P.⋆ element)
        → (fᴰ Pᴰ.⋆ᴰ elementᴰ) Pᴰ.≡[ fπ≡gπ ] (gᴰ Pᴰ.⋆ᴰ elementᴰ)
        → fᴰ D.≡[ extensionality fπ≡gπ ] gᴰ
      extensionalityᴰ fπ≡gπ p = R.rectify $
        cong snd (∫ue.extensionality (ΣPathP (fπ≡gπ , p)))

      introᴰ-natural : ∀ {x y}{f : C [ x , y ]}{p : P.p[ y ]}
        {xᴰ yᴰ}{fᴰ : D [ f ][ xᴰ , yᴰ ]}{pᴰ : Pᴰ.p[ p ][ yᴰ ]}
        → (fᴰ D.⋆ᴰ introᴰ _ pᴰ) D.≡[ intro-natural ] introᴰ _ (fᴰ Pᴰ.⋆ᴰ pᴰ)
      introᴰ-natural = R.rectify $ cong snd (∫ue.intro-natural)

-- A vertical presheaf is a displayed presheaf over a representable
Presheafⱽ : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → (c : C .Category.ob) → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-suc ℓC')) ℓD) ℓD')
                        (ℓ-suc ℓPᴰ))
Presheafⱽ D c = Presheafᴰ D (YO ⟅ c ⟆)

module PresheafⱽNotation
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {c} {ℓPᴰ} (P : Presheafⱽ Cᴰ c ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    variable
      x y z : C.ob
      f g h : C [ x , y ]
      cᴰ : Cᴰ.ob[ c ]
      xᴰ yᴰ zᴰ : Cᴰ.ob[ x ]
  open PresheafᴰNotation P public

  -- opaque or transparent?
  pⱽ[_] : (cᴰ : Cᴰ.ob[ c ]) → Type ℓPᴰ
  pⱽ[ cᴰ ] = p[ C.id ][ cᴰ ]

  _⋆ᴰⱽ_ :
      Cᴰ [ f ][ xᴰ , cᴰ ] → pⱽ[ cᴰ ]
      → p[ f ][ xᴰ ]
  fᴰ ⋆ᴰⱽ gⱽ = reind (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ)

  opaque
    ⋆ᴰid≡⋆ᴰⱽ : ∀ (fᴰ : Cᴰ [ f ][ xᴰ , cᴰ ]) (gⱽ : pⱽ[ cᴰ ])
      → fᴰ ⋆ᴰ gⱽ ≡[ C.⋆IdR f ] fᴰ ⋆ᴰⱽ gⱽ
    ⋆ᴰid≡⋆ᴰⱽ fᴰ gⱽ = reind-filler (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ)

actⱽ : {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
          → {x : C .Category.ob} → {ℓP : Level}
  → (Pⱽ : Presheafⱽ Cᴰ x ℓP)
  → ∀ {y}{yᴰ xᴰ} {f : C [ y , x ]}
  → Cᴰ [ f ][ yᴰ , xᴰ ]
  → ⟨ Pⱽ .F-obᴰ xᴰ (C .Category.id) ⟩
  → ⟨ Pⱽ .F-obᴰ yᴰ f ⟩
actⱽ {C = C} Pⱽ fᴰ pⱽ =
  subst (λ f → ⟨ Pⱽ .F-obᴰ _ f ⟩) (C .Category.⋆IdR _) (Pⱽ .F-homᴰ  fᴰ _ pⱽ)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         (x : C .Category.ob) (Pⱽ : Presheafⱽ Cᴰ x ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module RCᴰ = Reasoning Cᴰ
    module Pⱽ = PresheafⱽNotation Pⱽ

  -- A UniversalElementⱽ is the same as a UniversalElementᴰ but stated
  -- in terms of ⋆ᴰⱽ instead of ⋆ᴰ.
  record UniversalElementⱽ
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓPᴰ) where
    field
      vertexⱽ : Cᴰ.ob[ x ]
      elementⱽ : Pⱽ.pⱽ[ vertexⱽ ]
      universalⱽ : ∀ {y yᴰ}{f : C [ y , x ]} →
        isIso λ (fᴰ : Cᴰ [ f ][ yᴰ , vertexⱽ ]) → fᴰ Pⱽ.⋆ᴰⱽ elementⱽ

    toUniversalᴰ : UniversalElementᴰ Cᴰ Pⱽ (selfUnivElt C x)
    toUniversalᴰ .UniversalElementᴰ.vertexᴰ = vertexⱽ
    toUniversalᴰ .UniversalElementᴰ.elementᴰ = elementⱽ
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.inv f fᴰ =
      universalⱽ .fst fᴰ
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.rightInv f fᴰ =
      Pⱽ.rectify $ Pⱽ.≡out $
        (Pⱽ.≡in $ Pⱽ.⋆ᴰid≡⋆ᴰⱽ _ _)
        ∙ (Pⱽ.≡in $ universalⱽ .snd .fst fᴰ)
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.leftInv f fᴰ =
      RCᴰ.rectify $ RCᴰ.≡out $
        (RCᴰ.≡in $ (λ i → universalⱽ .fst (Pⱽ.⋆ᴰid≡⋆ᴰⱽ fᴰ elementⱽ i)))
        ∙ (RCᴰ.≡in $ universalⱽ .snd .snd fᴰ)
  module UniversalElementⱽNotation (ueⱽ : UniversalElementⱽ) where
    open UniversalElementⱽ ueⱽ public
    open UniversalElementᴰNotation Cᴰ Pⱽ (UniversalElementⱽ.toUniversalᴰ ueⱽ)
      public
    βⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {pᴰ : Pⱽ.p[ f ][ yᴰ ]}
      → introᴰ f pᴰ Pⱽ.⋆ᴰⱽ elementⱽ ≡ pᴰ
    βⱽ = universalⱽ .snd .fst _

    ηⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {fᴰ : Cᴰ [ f ][ yᴰ , vertexⱽ ]}
      → fᴰ ≡ introᴰ f (fᴰ Pⱽ.⋆ᴰⱽ elementⱽ)
    ηⱽ = sym (universalⱽ .snd .snd _)
