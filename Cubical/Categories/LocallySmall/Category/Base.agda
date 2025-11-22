module Cubical.Categories.LocallySmall.Category.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.LocallySmall.Variables.Base

open Σω
open Liftω

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

  Ob : Typeω
  Ob = ob

open Category

_^op : ∀ {Cob}{CHom-ℓ} → Category Cob CHom-ℓ → Category Cob λ x y → CHom-ℓ y x
(C ^op) .Hom[_,_] x y = C .Hom[_,_] y x
(C ^op) .id = C .id
(C ^op) ._⋆_ f g = C ._⋆_ g f
(C ^op) .⋆IdL = C .⋆IdR
(C ^op) .⋆IdR = C .⋆IdL
(C ^op) .⋆Assoc f g h = sym (C .⋆Assoc _ _ _)
(C ^op) .isSetHom = C .isSetHom

module _ (C : Category Cob CHom-ℓ) where
  private
    module C = Category C

  record CatIso (x y : Cob) : Type (ℓ-max (CHom-ℓ x x) $ ℓ-max (CHom-ℓ y y) $ ℓ-max (CHom-ℓ y x) (CHom-ℓ x y)) where
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
