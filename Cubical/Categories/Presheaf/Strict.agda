{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Strict where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Strictify
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.StrictHom
import Cubical.Categories.Presheaf.More as PshMore


open Functor
open Iso
open NatIso
open NatTrans

private
  variable
    ℓ ℓ' ℓP ℓQ ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓ ℓ'} (P : Presheaf C ℓP) where
  YonedaStrictifyPsh : Presheaf (YonedaStrictify C) _
  YonedaStrictifyPsh .F-ob c .fst = PshHomStrict (C [-, c ]) P
  YonedaStrictifyPsh .F-ob c .snd = isSetPshHomStrict _ _
  YonedaStrictifyPsh .F-hom f p = f ⋆PshHomStrict p
  YonedaStrictifyPsh .F-id = refl
  YonedaStrictifyPsh .F-seq = λ _ _ → refl

  -- Does it need to be YonedaStrictify C or can it be in C?
  -- YonedaStrictifyPsh : Presheaf C _
  -- YonedaStrictifyPsh .F-ob c .fst = PshHomStrict (C [-, c ]) P
  -- YonedaStrictifyPsh .F-ob c .snd = isSetPshHomStrict _ _
  -- YonedaStrictifyPsh .F-hom {x = x}{y = y} f p = compf ⋆PshHomStrict p
  --   where

  --   compf : PshHomStrict (C [-, y ]) (C [-, x ])
  --   compf .PshHomStrict.N-ob c = C._⋆ f
  --   compf .PshHomStrict.N-hom _ _ f g h ≡h = sym (C.⋆Assoc _ _ _) ∙ C.⟨ ≡h ⟩⋆⟨ refl ⟩
  -- It does need to be YonedaStrictify C for this to be refl
  -- YonedaStrictifyPsh .F-id = {!refl!}
  -- YonedaStrictifyPsh .F-seq = λ _ _ → {!!}

  private
    module P = PshMore.PresheafNotation P

  YonedaStrictifyPsh≅ : PshIsoStrict P (YonedaStrictifyPsh ∘F (toYonedaStrictify C ^opF))
  YonedaStrictifyPsh≅ .PshIsoStrict.trans .PshHomStrict.N-ob c = yoRecStrict P
  YonedaStrictifyPsh≅ .PshIsoStrict.trans .PshHomStrict.N-hom _ _ f p p' p≡ =
    makePshHomStrictPath (funExt λ _ → funExt λ _ → P.⋆Assoc _ _ _ ∙ P.⟨⟩⋆⟨ p≡ ⟩)
  YonedaStrictifyPsh≅ .PshIsoStrict.nIso c .fst = λ z → z .PshHomStrict.N-ob c (Category.id C)
  YonedaStrictifyPsh≅ .PshIsoStrict.nIso c .snd .fst b =
    makePshHomStrictPath (funExt λ _ → funExt λ _ → b .PshHomStrict.N-hom _ c _ _ _ (C .Category.⋆IdR _))
  YonedaStrictifyPsh≅ .PshIsoStrict.nIso c .snd .snd _ = P.⋆IdL _

module PresheafNotation {ℓo}{ℓh} {C' : Category ℓo ℓh} {ℓp} (P' : Presheaf C' ℓp) where
  private
    C = YonedaStrictify C'
    P = YonedaStrictifyPsh P'
    module C = Category C
  p[_] : C.ob → Type _
  p[ x ] = ⟨ P ⟅ x ⟆ ⟩

  infixr 9 _⋆_
  _⋆_ : ∀ {x y} (f : C [ x , y ]) (g : p[ y ]) → p[ x ]
  f ⋆ g = f ⋆PshHomStrict g

  ⋆IdL : ∀ {x} (g : p[ x ]) → C.id ⋆ g ≡ g
  ⋆IdL = λ _ → refl

  ⋆Assoc : ∀ {x y z} (f : C [ x , y ])(g : C [ y , z ])(h : p[ z ]) →
    (f C.⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
  ⋆Assoc f g _ = refl

  ⟨_⟩⋆⟨_⟩ : ∀ {x y} {f f' : C [ x , y ]} {g g' : p[ y ]}
            → f ≡ f' → g ≡ g' → f ⋆ g ≡ f' ⋆ g'
  ⟨ f≡f' ⟩⋆⟨ g≡g' ⟩ = cong₂ _⋆_ f≡f' g≡g'

  ⟨⟩⋆⟨_⟩ : ∀ {x y} {f : C [ x , y ]} {g g' : p[ y ]}
            → g ≡ g' → f ⋆ g ≡ f ⋆ g'
  ⟨⟩⋆⟨_⟩ = ⟨ refl ⟩⋆⟨_⟩

  ⟨_⟩⋆⟨⟩ : ∀ {x y} {f f' : C [ x , y ]} {g : p[ y ]}
            → f ≡ f' → f ⋆ g ≡ f' ⋆ g
  ⟨_⟩⋆⟨⟩ = ⟨_⟩⋆⟨ refl ⟩

  isSetPsh : ∀ {x} → isSet (p[ x ])
  isSetPsh {x} = (P ⟅ x ⟆) .snd
