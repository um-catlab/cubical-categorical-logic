{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Functor

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ : Level

open Functor
open Functorᴰ

-- IMO the order of D and P here should be swapped to match Functorᴰ
Presheafᴰ : {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (D : Categoryᴰ C ℓD ℓD')
          → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-suc ℓP))
                    (ℓ-suc ℓPᴰ))
Presheafᴰ {ℓP = ℓP} P D ℓPᴰ = Functorᴰ P (D ^opᴰ) (SETᴰ ℓP ℓPᴰ)

PRESHEAFᴰ : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → ∀ (ℓP ℓPᴰ : Level) → Categoryᴰ (PresheafCategory C ℓP) _ _
PRESHEAFᴰ Cᴰ ℓP ℓPᴰ = FUNCTORᴰ (Cᴰ ^opᴰ) (SETᴰ ℓP ℓPᴰ)

∫P : {C : Category ℓC ℓC'} {D : Categoryᴰ C ℓD ℓD'}
     → {P : Presheaf C ℓP} → {ℓPᴰ : Level}
     → Presheafᴰ P D ℓPᴰ
     → Presheaf (TotalCat.∫C D) (ℓ-max ℓP ℓPᴰ)
∫P Pᴰ = ΣF ∘F TotalCat.∫F Pᴰ

module PresheafᴰNotation {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓD ℓD'}
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
  infixr 9 _⋆ᴰ_
  infix 2 _≡[_]_

  pob[_] : C.ob → Type ℓP
  pob[ x ] = P.p[ x ]

  p[_][_] : ∀ {x} → P.p[ x ] → Cᴰ.ob[ x ] → Type ℓPᴰ
  p[ f ][ xᴰ ] = ⟨ Pᴰ .F-obᴰ xᴰ f ⟩

  isSetPshᴰ : ∀ {x}{p : P.p[ x ]}{xᴰ} → isSet p[ p ][ xᴰ ]
  isSetPshᴰ {x} {p} {xᴰ} = Pᴰ .F-obᴰ xᴰ p .snd

  _≡[_]_ : ∀ {x xᴰ} {f g : P.p[ x ]} → p[ f ][ xᴰ ] → f ≡ g → p[ g ][ xᴰ ]
    → Type ℓPᴰ
  _≡[_]_ {x} {xᴰ} {f} {g} fᴰ f≡g gᴰ =
    PathP (λ i → p[ f≡g i ][ xᴰ ]) fᴰ gᴰ

  reind : ∀ {x}{xᴰ}{f g : P.p[ x ]}(f≡g : f ≡ g)
      → p[ f ][ xᴰ ] → p[ g ][ xᴰ ]
  reind = subst p[_][ _ ]

  reind-filler : ∀ {x}{xᴰ}{f g : P.p[ x ]}(f≡g : f ≡ g)
    → (fᴰ : p[ f ][ xᴰ ])
    → (f , fᴰ) ≡ (g , reind f≡g fᴰ)
  reind-filler f≡g fᴰ = ΣPathP (f≡g , (subst-filler p[_][ _ ] f≡g fᴰ))

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
  rectify {fᴰ = fᴰ} {gᴰ = gᴰ} = subst (fᴰ ≡[_] gᴰ) (P.isSetPsh _ _ _ _)

  open PresheafNotation (∫P Pᴰ) public

  _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{g}
     → Cᴰ [ f ][ xᴰ , yᴰ ] → p[ g ][ yᴰ ]
     → p[ f P.⋆ g ][ xᴰ ]
  fᴰ ⋆ᴰ gᴰ = ((_ , fᴰ) ⋆ (_ , gᴰ)) .snd

  ⋆Assocᴰ : ∀ {x y z} {f : C [ x , y ]} {g : C [ y , z ]}  {h : P.p[ z ]} {xᴰ yᴰ zᴰ}
      (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ [ g ][ yᴰ , zᴰ ]) (hᴰ : p[ h ][ zᴰ ])
      → (fᴰ Cᴰ.⋆ᴰ gᴰ) ⋆ᴰ hᴰ ≡[ P.⋆Assoc f g h ] fᴰ ⋆ᴰ (gᴰ ⋆ᴰ hᴰ)
  ⋆Assocᴰ fᴰ gᴰ hᴰ = rectify $ ≡out $ ⋆Assoc (_ , fᴰ) (_ , gᴰ) (_ , hᴰ)

  ⋆IdLᴰ : ∀ {x} {f : P.p[ x ]} {xᴰ} (fᴰ : p[ f ][ xᴰ ]) → Cᴰ.idᴰ ⋆ᴰ fᴰ ≡[ P.⋆IdL f ] fᴰ
  ⋆IdLᴰ fᴰ = rectify $ ≡out $ ⋆IdL (_ , fᴰ)

  _⋆ⱽᴰ_ : ∀ {x xᴰ xᴰ'}{g}
     → Cᴰ [ C.id {x} ][ xᴰ , xᴰ' ] → p[ g ][ xᴰ' ]
     → p[ g ][ xᴰ ]
  fⱽ ⋆ⱽᴰ gᴰ = reind (P.⋆IdL _) (fⱽ ⋆ᴰ gᴰ)

  opaque
    ⋆Assocᴰⱽᴰ : ∀ {x y} {f : C [ x , y ]} {h : P.p[ y ]} {xᴰ yᴰ yᴰ'}
        (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (gⱽ : Cᴰ.v[ y ] [ yᴰ , yᴰ' ]) (hᴰ : p[ h ][ yᴰ' ])
        → Path p[ _ ]
            (_ , ((fᴰ Cᴰ.⋆ᴰⱽ gⱽ) ⋆ᴰ hᴰ))
            (_ , (fᴰ ⋆ᴰ (gⱽ ⋆ⱽᴰ hᴰ)))
    ⋆Assocᴰⱽᴰ fᴰ gⱽ hᴰ =
      ⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
      ∙ ⋆Assoc _ _ _
      ∙ ⟨ refl ⟩⋆⟨ reind-filler _ _ ⟩

    ⋆ⱽIdL : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{g}
      → (gᴰ : p[ g ][ xᴰ ])
      → Cᴰ.idᴰ ⋆ⱽᴰ gᴰ ≡ gᴰ
    ⋆ⱽIdL gᴰ = rectify $ ≡out $ (sym $ reind-filler _ _) ∙ ⋆IdL _

    -- TODO: ⋆ⱽAssoc but it relies on the definition _⋆ⱽ_ in the fiber

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
         {P : Presheaf C ℓP} (ue : UniversalElement C P) (Pᴰ : Presheafᴰ P D ℓPᴰ) where
  private
    module D = Categoryᴰ D
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ

  record UniversalElementᴰ
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-max ℓP ℓPᴰ)) where
    open UniversalElementNotation ue
    field
      vertexᴰ : D.ob[ vertex ]
      elementᴰ : Pᴰ.p[ element ][ vertexᴰ ]
      universalᴰ : ∀ {x xᴰ} →
        isIsoOver (equivToIso (_ , (universal x)))
          D.Hom[_][ xᴰ , vertexᴰ ]
          (λ p → Pᴰ.p[ p ][ xᴰ ])
          λ f fᴰ → fᴰ Pᴰ.⋆ᴰ elementᴰ

    ∫ue : UniversalElement (TotalCat.∫C D) (∫P Pᴰ)
    ∫ue .UniversalElement.vertex = vertex , vertexᴰ
    ∫ue .UniversalElement.element = element , elementᴰ
    ∫ue .UniversalElement.universal (v , vᴰ) =
      isIsoToIsEquiv (isIsoOver→isIsoΣ (universalᴰ))

    module ∫ue = UniversalElementNotation ∫ue
    module Pshᴰ = PresheafᴰNotation Pᴰ

    introᴰ : ∀ {x xᴰ} {p : P.p[ x ]}
        → Pᴰ.p[ p ][ xᴰ ]
        → D [ intro p ][ xᴰ , vertexᴰ ]
    introᴰ {p = p} pᴰ = ∫ue.intro (p , pᴰ) .snd

    introᴰ≡ = ∫ue.intro≡
    introᴰ-natural = ∫ue.intro-natural
    extensionalityᴰ = ∫ue.extensionality
    βᴰ = ∫ue.β
    ηᴰ = ∫ue.η
    weak-ηᴰ = ∫ue.weak-η

-- A vertical presheaf is a displayed presheaf over a representable
Presheafⱽ : {C : Category ℓC ℓC'} (c : C .Category.ob) (D : Categoryᴰ C ℓD ℓD')
          → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-suc ℓC')) ℓD) ℓD')
                        (ℓ-suc ℓPᴰ))
Presheafⱽ {C = C} c D = Presheafᴰ (YO {C = C} ⟅ c ⟆) D

module PresheafⱽNotation
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {c} {ℓPᴰ} (P : Presheafⱽ c Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
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

  ⋆ᴰid≡⋆ᴰⱽ : ∀ (fᴰ : Cᴰ [ f ][ xᴰ , cᴰ ]) (gⱽ : pⱽ[ cᴰ ])
    → fᴰ ⋆ᴰ gⱽ ≡[ C.⋆IdR f ] fᴰ ⋆ᴰⱽ gⱽ
  ⋆ᴰid≡⋆ᴰⱽ fᴰ gⱽ = λ i → reind-filler (C.⋆IdR _) (fᴰ ⋆ᴰ gⱽ) i .snd

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         (x : C .Category.ob) (Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module Pⱽ = PresheafⱽNotation Pⱽ

  -- A UniversalElementⱽ is equivalent to a UniversalElementᴰ but
  -- stated in terms of Pⱽ.⋆ᴰⱽ instead of Pⱽ.⋆ᴰ, so the universality
  -- property is simpler.

  record UniversalElementⱽ
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓPᴰ) where
    field
      vertexⱽ : Cᴰ.ob[ x ]
      elementⱽ : Pⱽ.pⱽ[ vertexⱽ ]
      universalⱽ : ∀ {y yᴰ}{f : C [ y , x ]} →
        isIso λ (fᴰ : Cᴰ [ f ][ yᴰ , vertexⱽ ]) → fᴰ Pⱽ.⋆ᴰⱽ elementⱽ

    toUniversalᴰ : UniversalElementᴰ Cᴰ (selfUnivElt C x) Pⱽ
    toUniversalᴰ .UniversalElementᴰ.vertexᴰ = vertexⱽ
    toUniversalᴰ .UniversalElementᴰ.elementᴰ = elementⱽ
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.inv f fᴰ =
      universalⱽ .fst fᴰ
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.rightInv f fᴰ =
      Pⱽ.rectify $ Pⱽ.≡out $
        (Pⱽ.≡in $ Pⱽ.⋆ᴰid≡⋆ᴰⱽ _ _)
        ∙ (Pⱽ.≡in $ universalⱽ .snd .fst fᴰ)
    toUniversalᴰ .UniversalElementᴰ.universalᴰ .isIsoOver.leftInv f fᴰ =
      Cᴰ.rectify $ Cᴰ.≡out $
        (Cᴰ.≡in $ (λ i → universalⱽ .fst (Pⱽ.⋆ᴰid≡⋆ᴰⱽ fᴰ elementⱽ i)))
        ∙ (Cᴰ.≡in $ universalⱽ .snd .snd fᴰ)

    open UniversalElementᴰ toUniversalᴰ hiding (module Pshᴰ) public
    module Pshⱽ = PresheafⱽNotation Pⱽ

    introⱽ : ∀ {xᴰ} → Pⱽ.p[ C.id ][ xᴰ ] → Cᴰ.v[ x ] [ xᴰ , vertexᴰ ]
    introⱽ = introᴰ

    βⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {pᴰ : Pⱽ.p[ f ][ yᴰ ]}
      → introᴰ pᴰ Pⱽ.⋆ᴰⱽ elementⱽ ≡ pᴰ
    βⱽ = universalⱽ .snd .fst _

    ηⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {fᴰ : Cᴰ [ f ][ yᴰ , vertexⱽ ]}
      → fᴰ ≡ introᴰ (fᴰ Pⱽ.⋆ᴰⱽ elementⱽ)
    ηⱽ = sym (universalⱽ .snd .snd _)
