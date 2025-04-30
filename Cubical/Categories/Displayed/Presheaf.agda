{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber hiding (⋆Assocᴰⱽᴰ)
open import Cubical.Categories.Constructions.TotalCategory hiding (intro)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Displayed.Reasoning as Reasoning
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor

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

module _ {C : Category ℓC ℓC'} {D : Categoryᴰ C ℓD ℓD'}
       {P : Presheaf C ℓP} {ℓPᴰ : Level}
       (Pᴰ : Presheafᴰ D P ℓPᴰ) where
  private
    module P = PresheafReasoning P

  ∫P : Presheaf (∫C D) (ℓ-max ℓP ℓPᴰ)
  ∫P .F-ob (x , xᴰ) .fst = Σ ⟨ P ⟅ x ⟆ ⟩ (λ p → ⟨ Pᴰ .F-obᴰ xᴰ p ⟩)
  ∫P .F-ob (x , xᴰ) .snd = isSetΣ (P .F-ob x .snd) (λ p → F-obᴰ Pᴰ xᴰ p .snd)
  ∫P .F-hom (f , fᴰ) (p , pᴰ) = (f P.⋆ᴾ p) , Pᴰ .F-homᴰ fᴰ p pᴰ
  ∫P .F-id = funExt λ (p , pᴰ) → ΣPathP ((P.⋆ᴾId p) , λ i → Pᴰ .F-idᴰ i p pᴰ)
  ∫P .F-seq (f , fᴰ) (g , gᴰ) i (p , pᴰ) =
    P.⋆ᴾAssoc g f p i , Pᴰ .F-seqᴰ fᴰ gᴰ i p pᴰ

module PresheafᴰReasoning {C : Category ℓC ℓC'} {D : Categoryᴰ C ℓD ℓD'}
       {P : Presheaf C ℓP} {ℓPᴰ : Level}
       (Pᴰ : Presheafᴰ D P ℓPᴰ)
       where
  private
    module D = Categoryᴰ D
    module DR = Reasoning D
    module P = PresheafReasoning P

  _≡[_]_ :
    ∀ {x xᴰ} {f g : ⟨ P ⟅ x ⟆ ⟩}
    → ⟨ Pᴰ .F-obᴰ xᴰ f ⟩ → f ≡ g → ⟨ Pᴰ .F-obᴰ xᴰ g ⟩
    → Type ℓPᴰ
  _≡[_]_ {x} {xᴰ} {f} {g} fᴰ p gᴰ = PathP (λ i → ⟨ Pᴰ .F-obᴰ xᴰ (p i) ⟩) fᴰ gᴰ

  _⋆ᴰ_ : ∀ {x y xᴰ yᴰ}{f : C [ x , y ]}{p}
      (fᴰ : D [ f ][ xᴰ , yᴰ ])(pᴰ : ⟨ Pᴰ .F-obᴰ yᴰ p ⟩)
      → ⟨ Pᴰ .F-obᴰ xᴰ (f P.⋆ᴾ p) ⟩
  fᴰ ⋆ᴰ pᴰ  = Pᴰ .F-homᴰ fᴰ _ pᴰ
  open PresheafReasoning (∫P Pᴰ) public
  -- see Cubical.Categories.Displayed.Reasoning for an overview of this API
  module _ {x : C .ob} {p q : ⟨ P ⟅ x ⟆ ⟩}
    {xᴰ : D.ob[ x ]}
    {pᴰ : ⟨ Pᴰ .F-obᴰ xᴰ p ⟩}
    {qᴰ : ⟨ Pᴰ .F-obᴰ xᴰ q ⟩} where
    ≡in : {eq : p ≡ q}
      → (eqᴰ : pᴰ ≡[ eq ] qᴰ)
      → (p , pᴰ) ≡ (q , qᴰ)
    ≡in eqᴰ = ΣPathP (_ , eqᴰ)

    ≡out : (∫eq : (p , pᴰ) ≡ (q , qᴰ))
      → pᴰ ≡[ PathPΣ ∫eq .fst ] qᴰ
    ≡out ∫eq = PathPΣ ∫eq .snd

  module _ {x : C .ob}{p q : ⟨ P ⟅ x ⟆ ⟩}
    (eq : p ≡ q)
    {xᴰ : D.ob[ x ]}
    (pᴰ : ⟨ Pᴰ .F-obᴰ xᴰ p ⟩) where
    opaque 
      reind : ⟨ Pᴰ .F-obᴰ xᴰ q ⟩
      reind = subst (λ p → ⟨ Pᴰ .F-obᴰ xᴰ p ⟩) eq pᴰ

      reind-filler : (p , pᴰ) ≡ (q , reind)
      reind-filler = ΣPathP (eq , (subst-filler (λ p → ⟨ Pᴰ .F-obᴰ xᴰ p ⟩) eq pᴰ))

  opaque 
    rectify : {x : C .ob}{p q : ⟨ P ⟅ x ⟆ ⟩}
      {eq eq' : p ≡ q}
      {xᴰ : D.ob[ x ]}
      {pᴰ : ⟨ Pᴰ .F-obᴰ xᴰ p ⟩}
      {qᴰ : ⟨ Pᴰ .F-obᴰ xᴰ q ⟩}
      → pᴰ ≡[ eq ] qᴰ → pᴰ ≡[ eq' ] qᴰ
    rectify {pᴰ = pᴰ}{qᴰ = qᴰ} = subst (pᴰ ≡[_] qᴰ) (P .F-ob _ .snd _ _ _ _)

  _⋆ⱽᴰ_ : ∀ {x xᴰ xᴰ'}{p}
    (v : D [ C .id {x} ][ xᴰ , xᴰ' ])(pᴰ : ⟨ Pᴰ .F-obᴰ xᴰ' p ⟩)
    → ⟨ Pᴰ .F-obᴰ xᴰ p ⟩
  v ⋆ⱽᴰ pᴰ = reind (P.⋆ᴾId _) (v ⋆ᴰ pᴰ)

  ⋆Assocᴰⱽᴰ : ∀ {x y} {f : C [ x , y ]} {p : ⟨ P ⟅ y ⟆ ⟩}
    {xᴰ yᴰ yᴰ'}
    (fᴰ : D [ f ][ xᴰ , yᴰ ])
    (v : D [ C .id ][ yᴰ , yᴰ' ])
    (pᴰ : ⟨ Pᴰ .F-obᴰ yᴰ' p ⟩)
    → ((fᴰ ⋆ᴰⱽ⟨ D ⟩ v) ⋆ᴰ pᴰ) ≡ (fᴰ ⋆ᴰ (v ⋆ⱽᴰ pᴰ))
  ⋆Assocᴰⱽᴰ fᴰ v pᴰ = rectify $ ≡out $
    ⟨ sym $ DR.reind-filler _ _ ⟩⋆ᴾ⟨ refl ⟩
    ∙ ⋆ᴾAssoc _ _ _
    ∙ ⟨ refl ⟩⋆ᴾ⟨ reind-filler _ _ ⟩

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ D P ℓPᴰ) where

  record UniversalElementᴰ (ue : UniversalElement C P)
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-max ℓP ℓPᴰ)) where
    open UniversalElementNotation ue
    open Categoryᴰ D
    field
      vertexᴰ : ob[ vertex ]
      elementᴰ : ⟨ Pᴰ .F-obᴰ vertexᴰ element ⟩
      universalᴰ : ∀ {x xᴰ} →
        isIsoOver (equivToIso (_ , (universal x)))
          Hom[_][ xᴰ , vertexᴰ ]
          (λ p → ⟨ Pᴰ .F-obᴰ xᴰ p ⟩)
          λ f fᴰ → Pᴰ .F-homᴰ fᴰ element elementᴰ
    open isIsoOver
    private
      module D = Categoryᴰ D
      module DR = Reasoning D
      module Pᴰ = PresheafᴰReasoning Pᴰ
    introᴰ : ∀ {x xᴰ} (p : ⟨ P ⟅ x ⟆ ⟩)
        → ⟨ Pᴰ .F-obᴰ xᴰ p ⟩
        → D [ intro p ][ xᴰ , vertexᴰ ]
    introᴰ p pᴰ = universalᴰ .inv p pᴰ

    introᴰ⟨_⟩ : ∀ {x xᴰ} {p q : ⟨ P ⟅ x ⟆ ⟩} {p≡q : p ≡ q}
        {pᴰ : ⟨ Pᴰ .F-obᴰ xᴰ p ⟩} {qᴰ : ⟨ Pᴰ .F-obᴰ xᴰ q ⟩}
        → (pᴰ Pᴰ.≡[ p≡q ] qᴰ)
        → introᴰ p pᴰ D.≡[ cong intro p≡q ] introᴰ q qᴰ
    introᴰ⟨ pᴰ≡qᴰ ⟩ i = introᴰ _ (pᴰ≡qᴰ i)

    βᴰ : ∀ {x xᴰ} {p : ⟨ P ⟅ x ⟆ ⟩} {pᴰ : ⟨ Pᴰ .F-obᴰ xᴰ p ⟩}
         → PathP (λ i → ⟨ Pᴰ .F-obᴰ xᴰ (β {p = p} i) ⟩)
             (Pᴰ .F-homᴰ (introᴰ p pᴰ) element elementᴰ)
             pᴰ
    βᴰ = universalᴰ .rightInv _ _

    ηᴰ : ∀ {x xᴰ} {f : C [ x , vertex ]} {fᴰ : D [ f ][ xᴰ , vertexᴰ ]}
         → fᴰ ≡[ η {f = f} ] introᴰ _ (F-homᴰ Pᴰ fᴰ element elementᴰ)
    ηᴰ = symP (universalᴰ .leftInv _ _)

    extensionalityᴰ :
      ∀ {x xᴰ}{f f' : C [ x , vertex ]}{fP≡f'P}
      → {fᴰ : D [ f ][ xᴰ , vertexᴰ ]}
      → {fᴰ' : D [ f' ][ xᴰ , vertexᴰ ]}
      → (fᴰ Pᴰ.⋆ᴰ elementᴰ) Pᴰ.≡[ fP≡f'P ] (fᴰ' Pᴰ.⋆ᴰ elementᴰ)
      → fᴰ ≡[ extensionality fP≡f'P ] fᴰ'
    extensionalityᴰ {fᴰ = fᴰ}{fᴰ'} fᴰP≡fᴰ'P = DR.rectify $ DR.≡out $
      isoFunInjective (isoOver→Iso (isIsoOver→IsoOver universalᴰ))
        (_ , fᴰ) (_ , fᴰ')
        (ΣPathP $ _ , fᴰP≡fᴰ'P)

-- A vertical presheaf is a displayed presheaf over a representable
Presheafⱽ : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → (c : C .ob) → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-suc ℓC')) ℓD) ℓD')
                        (ℓ-suc ℓPᴰ))
Presheafⱽ D c = Presheafᴰ D (YO ⟅ c ⟆)

module PresheafⱽReasoning {C : Category ℓC ℓC'} {D : Categoryᴰ C ℓD ℓD'}
       {c : C .ob} {ℓPᴰ : Level}
       (Pⱽ : Presheafⱽ D c ℓPᴰ)
       where
  private
    module D = Categoryᴰ D
  open PresheafᴰReasoning Pⱽ public
  opaque
    _⋆ᴰⱽ_ : ∀ {x xᴰ cᴰ}{f : C [ x , c ]}
      (fᴰ : D [ f ][ xᴰ , cᴰ ])(pⱽ : ⟨ Pⱽ .F-obᴰ cᴰ (C .id) ⟩)
      → ⟨ Pⱽ .F-obᴰ xᴰ f ⟩
    fᴰ ⋆ᴰⱽ pⱽ = reind (C .⋆IdR _) (fᴰ ⋆ᴰ pⱽ)

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
