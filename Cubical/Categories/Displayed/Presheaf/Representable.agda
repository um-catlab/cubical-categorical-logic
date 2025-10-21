{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Representable where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category as Small
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.LocallySmall as LocallySmall

open import Cubical.Categories.Displayed.Base as Small
open import Cubical.Categories.Displayed.More
import Cubical.Categories.Constructions.TotalCategory as Small
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Base hiding (PRESHEAFᴰ)
open import Cubical.Categories.Displayed.Presheaf.Properties
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Section

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open Category
open isIsoOver
open Functor
open Functorᴰ
open isIsoOver
open PshHom
open PshIso
open PshHomᴰ
open Section

-- Displayed Yoneda
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ

  yoRecᴰ : ∀ {c}{cᴰ : Cᴰ.ob[ c ]} {p : P.p[ c ]}
    → (pᴰ : Pᴰ.p[ p ][ cᴰ ]) → PshHomᴰ (yoRec P p) (Cᴰ [-][-, cᴰ ]) Pᴰ
  yoRecᴰ pᴰ .N-obᴰ fᴰ = fᴰ Pᴰ.⋆ᴰ pᴰ
  yoRecᴰ pᴰ .N-homᴰ = Pᴰ.⋆Assoc _ _ _

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         {P : Presheaf C ℓP} (ue : UniversalElement C P) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
  open UniversalElementNotation ue

  isUniversalᴰ : (vertexᴰ : Cᴰ.ob[ vertex ]) → Pᴰ.p[ element ][ vertexᴰ ] → Type _
  isUniversalᴰ vertexᴰ elementᴰ = isPshIsoᴰ (yoRecᴰ Pᴰ elementᴰ) ⋆element-isPshIso

  record UniversalElementᴰ
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') (ℓ-max ℓP ℓPᴰ)) where
    constructor univeltᴰ
    field
      vertexᴰ : Cᴰ.ob[ vertex ]
      elementᴰ : Pᴰ.p[ element ][ vertexᴰ ]
      universalᴰ : isPshIsoᴰ (yoRecᴰ Pᴰ elementᴰ) ⋆element-isPshIso

    introᴰ : ∀ {x xᴰ} {p : P.p[ x ]}
        → Pᴰ.p[ p ][ xᴰ ]
        → Cᴰ [ intro p ][ xᴰ , vertexᴰ ]
    introᴰ = universalᴰ .fst

    ∫ue : UniversalElement (Small.∫C Cᴰ) (∫P Pᴰ)
    ∫ue .UniversalElement.vertex = vertex , vertexᴰ
    ∫ue .UniversalElement.element = element , elementᴰ
    ∫ue .UniversalElement.universal (v , vᴰ) =
      isIsoToIsEquiv
        ( (λ (p , pᴰ) → _ , (introᴰ pᴰ))
        , (λ (p , pᴰ) → universalᴰ .snd .fst pᴰ)
        , (λ (f , fᴰ) → universalᴰ .snd .snd fᴰ))

    module ∫ue = UniversalElementNotation ∫ue
    module Pshᴰ = PresheafᴰNotation Pᴰ

    -- We only provide the ∫ versions of these because working with
    -- the PathP versions is extremely slow.
    introᴰ≡ = ∫ue.intro≡
    introᴰ-natural = ∫ue.intro-natural
    extensionalityᴰ = ∫ue.extensionality
    βᴰ = ∫ue.β
    ηᴰ = ∫ue.η
    weak-ηᴰ = ∫ue.weak-η

    asPshIsoᴰ : PshCatIsoᴰ asPshIso (Cᴰ [-][-, vertexᴰ ]) Pᴰ
    asPshIsoᴰ =
      PshIsoᴰ→PshCatIsoᴰ _ _ _ (pshisoᴰ (yoRecᴰ Pᴰ elementᴰ) universalᴰ)

  open UniversalElementᴰ
  isUniversalᴰ→UniversalElementᴰ :
    ∀ {vᴰ eᴰ} (isUᴰ : isUniversalᴰ vᴰ eᴰ)
    → UniversalElementᴰ
  isUniversalᴰ→UniversalElementᴰ = univeltᴰ _ _

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
  open UniversalElement
  open UniversalElementᴰ
  subst-isUniversalᴰ :
    ∀ {v e e'}{e≡e' : e ≡ e'}{isU : isUniversal C P v e}
      {vᴰ eᴰ eᴰ'}(eᴰ≡eᴰ' : Path Pᴰ.p[ _ ] (_ , eᴰ) (_ , eᴰ'))
    (isUᴰ : isUniversalᴰ Cᴰ (isUniversal→UniversalElement P isU) Pᴰ vᴰ eᴰ)
    → isUniversalᴰ Cᴰ (isUniversal→UniversalElement P (subst-isUniversal P e≡e' isU)) Pᴰ vᴰ eᴰ'
  subst-isUniversalᴰ eᴰ≡eᴰ' isUᴰ .fst = isUᴰ .fst
  subst-isUniversalᴰ eᴰ≡eᴰ' isUᴰ .snd .fst pᴰ =
    Pᴰ.⟨⟩⋆⟨ sym eᴰ≡eᴰ' ⟩ ∙ isUᴰ .snd .fst pᴰ
  subst-isUniversalᴰ eᴰ≡eᴰ' isUᴰ .snd .snd fᴰ =
    introᴰ≡ (univeltᴰ _ _ isUᴰ) Pᴰ.⟨⟩⋆⟨ sym eᴰ≡eᴰ' ⟩

  subst-UniversalElementᴰ : ∀ {ue : UniversalElement C P}
    {e}{elt≡e : ue .element ≡ e}
    (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ)
    {eᴰ}
    (eltᴰ≡eᴰ : Path Pᴰ.p[ _ ] (_ , ueᴰ .elementᴰ) (_ , eᴰ))
    → UniversalElementᴰ Cᴰ (subst-UniversalElement P ue elt≡e) Pᴰ
  subst-UniversalElementᴰ ueᴰ eltᴰ≡eᴰ = univeltᴰ _ _ (subst-isUniversalᴰ eltᴰ≡eᴰ (ueᴰ .universalᴰ))

  UEᴰ-essUniq : {ue ue' : UniversalElement C P}
    → (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ)
    → (ueᴰ' : UniversalElementᴰ Cᴰ ue' Pᴰ)
    → Small.CatIsoᴰ Cᴰ (UE-essUniq P ue ue') (ueᴰ .vertexᴰ) (ueᴰ' .vertexᴰ)
  UEᴰ-essUniq ueᴰ ueᴰ' =
    ∫iso .fst .snd , isisoᴰ
    (∫iso .snd .Small.isIso.inv .snd)
    (Cᴰ.rectify $ Cᴰ.≡out $ ∫iso .snd .Small.isIso.sec)
    (Cᴰ.rectify $ Cᴰ.≡out $ ∫iso .snd .Small.isIso.ret)
    where
    ∫iso : Small.CatIso (Small.∫C Cᴰ) (_ , ueᴰ .vertexᴰ) (_ , ueᴰ' .vertexᴰ)
    ∫iso = UE-essUniq (∫P Pᴰ) (∫ue ueᴰ) (∫ue ueᴰ')

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
         {P : Presheaf C ℓP} {x} (yx≅P : PshCatIso (C [-, x ]) P)
         (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module PshC = LocallySmallCategoryNotation (PRESHEAF C)
    module Psh∫C = LocallySmallCategoryNotation (PRESHEAF (Small.∫C Cᴰ))
  open UniversalElementᴰ
  module _ {xᴰ} (yxᴰ≅Pᴰ : PshCatIsoᴰ yx≅P (Cᴰ [-][-, xᴰ ]) Pᴰ) where
    private
      ∫repr→ue : UniversalElement (Small.∫C Cᴰ) (∫P Pᴰ)
      ∫repr→ue =
        PshIso→UniversalElement (∫P Pᴰ) (Psh∫C.invCatIso (TotalCatYoPshIso Cᴰ)
          Psh∫C.ISOC.⋆ ∫PshCatIso yxᴰ≅Pᴰ)
      module ∫repr→ue = UniversalElementNotation ∫repr→ue
    PshIsoᴰ→UniversalElementᴰ : UniversalElementᴰ Cᴰ (PshIso→UniversalElement P yx≅P) Pᴰ
    PshIsoᴰ→UniversalElementᴰ .vertexᴰ = ∫repr→ue.vertex .snd
    PshIsoᴰ→UniversalElementᴰ .elementᴰ = ∫repr→ue.element .snd
    PshIsoᴰ→UniversalElementᴰ .universalᴰ {Γ} {Γᴰ} .fst {p} pᴰ = ∫repr→ue.intro (p , pᴰ) .snd
    PshIsoᴰ→UniversalElementᴰ .universalᴰ {Γ} {Γᴰ} .snd .fst {p} pᴰ = ∫repr→ue.β
    PshIsoᴰ→UniversalElementᴰ .universalᴰ {Γ} {Γᴰ} .snd .snd {f} fᴰ = sym $ ∫repr→ue.η

-- Vertical Universal properties are universal properties over
-- representable presheaves
--
-- There are several different ways to do this, each requiring
-- different amounts of transport:
-- 1. An element eⱽ : Pⱽ.p[ id ][ vⱽ ] such that vertical composition with it is an Iso. This is the old definition we had
-- 2. An element eⱽ : Pⱽ.p[ id ][ vⱽ ] that is a universal element over the selfUnivElt id {x}
-- 3. An element eⱽ : Pⱽ.p[ id~ ][ x ]
--
-- A vertical universal element is therefore over a morphism that is
-- *equal to* the identity.

-- module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
--          {x : C .Category.ob}{id~ : C [ x , x ]}(id≡id~ : C .Category.id ≡ id~)
--          (Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ) where
--   private
--     module C = Category C
--     module Cᴰ = Fibers Cᴰ
--     module Pⱽ = PresheafⱽNotation Pⱽ

--   UniversalElementⱽ : Type _
--   UniversalElementⱽ = UniversalElementᴰ Cᴰ
--     (subst-UniversalElement (C [-, x ]) (selfUnivElt C x) id≡id~)
--     Pⱽ

--   isUniversalⱽ : (vertexⱽ : Cᴰ.ob[ x ])(elementⱽ : Pⱽ.p[ id~ ][ vertexⱽ ]) → Type _
--   isUniversalⱽ = isUniversalᴰ Cᴰ (subst-UniversalElement (C [-, x ]) (selfUnivElt C x) id≡id~) Pⱽ

-- module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--          {x : C .Category.ob} {Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ} where
--   private
--     module C = Category C
--     module Cᴰ = Fibers Cᴰ
--     module Pⱽ = PresheafⱽNotation Pⱽ

--   open UniversalElementⱽ
--   fromUniversalᴰ : UniversalElementᴰ Cᴰ (selfUnivElt C x) Pⱽ → UniversalElementⱽ Cᴰ x Pⱽ
--   fromUniversalᴰ ueᴰ = record
--     { vertexⱽ = ueᴰ.vertexᴰ
--     ; elementⱽ = ueᴰ.elementᴰ
--     ; universalⱽ = (ueᴰ.universalᴰ .inv _)
--       , (λ pᴰ → Pⱽ.rectify $ Pⱽ.≡out $ (sym $ Pⱽ.reind-filler _ _) ∙ ueᴰ.βᴰ)
--       , λ fᴰ → Cᴰ.rectify $ Cᴰ.≡out $ ueᴰ.∫ue.intro⟨ sym $ Pⱽ.reind-filler _ _ ⟩ ∙ sym ueᴰ.ηᴰ
--     } where module ueᴰ = UniversalElementᴰ ueᴰ

--   module _ (ueⱽ : UniversalElementⱽ Cᴰ x Pⱽ) where
--     private
--       module ueⱽ = UniversalElementⱽ ueⱽ

--     yoRecIsoⱽ : PshIsoⱽ (Cᴰ [-][-, ueⱽ.vertexᴰ ]) Pⱽ
--     yoRecIsoⱽ .fst = yoRecⱽ Pⱽ ueⱽ.elementⱽ
--     yoRecIsoⱽ .snd = isisoover
--       (λ a → ueⱽ.universalⱽ .fst)
--       (λ b → ueⱽ.universalⱽ .snd .fst)
--       (λ a → ueⱽ.universalⱽ .snd .snd)

-- module _
--   {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {c} {Pⱽ : Presheafⱽ c Cᴰ ℓPᴰ}
--   where
--   open UniversalElementⱽ
--   open isIsoᴰ
--   private
--     module Cᴰ = Fibers Cᴰ
--     module Pⱽ = PresheafⱽNotation Pⱽ
--   UEⱽ-essUniq : (ueⱽ ueⱽ' : UniversalElementⱽ Cᴰ c Pⱽ) → CatIsoⱽ Cᴰ (ueⱽ .vertexⱽ) (ueⱽ' .vertexⱽ)
--   UEⱽ-essUniq ueⱽ ueⱽ' .fst = introⱽ ueⱽ' (elementⱽ ueⱽ)
--   UEⱽ-essUniq ueⱽ ueⱽ' .snd .invᴰ = introⱽ ueⱽ (elementⱽ ueⱽ')
--   UEⱽ-essUniq ueⱽ ueⱽ' .snd .secᴰ = Cᴰ.rectify $ Cᴰ.≡out $
--     UniversalElementᴰ.extensionalityᴰ (toUniversalᴰ ueⱽ') $
--     Pⱽ.⋆Assoc _ _ _
--     ∙ Pⱽ.⟨⟩⋆⟨ UniversalElementᴰ.βᴰ (toUniversalᴰ ueⱽ') ⟩
--     ∙ UniversalElementᴰ.βᴰ (toUniversalᴰ ueⱽ)
--     ∙ (sym $ Pⱽ.⋆IdL _)
--   UEⱽ-essUniq ueⱽ ueⱽ' .snd .retᴰ = Cᴰ.rectify $ Cᴰ.≡out $
--     UniversalElementᴰ.extensionalityᴰ (toUniversalᴰ ueⱽ) $
--     Pⱽ.⋆Assoc _ _ _
--     ∙ Pⱽ.⟨⟩⋆⟨ UniversalElementᴰ.βᴰ (toUniversalᴰ ueⱽ) ⟩
--     ∙ UniversalElementᴰ.βᴰ (toUniversalᴰ ueⱽ')
--     ∙ (sym $ Pⱽ.⋆IdL _)


module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {ue : UniversalElement C P}{α : PshCatIso P Q}
  where
  private
    module PshCᴰ = LocallySmallCategoryᴰNotation (PRESHEAFᴰ Cᴰ)
    module Pᴰ = PresheafᴰNotation Pᴰ
  _◁PshIsoᴰ_ : (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ) (αᴰ : PshCatIsoᴰ α Pᴰ Qᴰ)
    → UniversalElementᴰ Cᴰ (ue ◁PshIso α) Qᴰ
  ueᴰ ◁PshIsoᴰ αᴰ = subst-UniversalElementᴰ Cᴰ Qᴰ
    (PshIsoᴰ→UniversalElementᴰ Cᴰ _ Qᴰ
      (ueᴰ.asPshIsoᴰ PshCᴰ.ISOCᴰ.⋆ᴰ αᴰ)
      )
    αᴰ.N-obᴰ⟨ Pᴰ.⋆IdL _ ⟩
    where
      module ueᴰ = UniversalElementᴰ ueᴰ
      module αᴰ = PshHomᴰ (αᴰ .CatIsoᴰ.funᴰ)

-- module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {x}
--   {Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ}{Qⱽ : Presheafⱽ x Cᴰ ℓQᴰ}
--   where
--   _◁PshIsoⱽ_ : UniversalElementⱽ Cᴰ x Pⱽ → PshIsoⱽ Pⱽ Qⱽ → UniversalElementⱽ Cᴰ x Qⱽ
--   ueⱽ ◁PshIsoⱽ αⱽ = fromUniversalᴰ record
--     { vertexᴰ = ueⱽ◁αⱽ.vertexᴰ
--     ; elementᴰ = ueⱽ◁αⱽ.elementᴰ -- ueᴰ◁αⱽ.elementᴰ
--     ; universalᴰ = isisoover
--       (λ _ → ueⱽ◁αⱽ.introᴰ)
--       (λ _ _ → Qⱽ.rectify $ Qⱽ.≡out $ ueⱽ◁αⱽ.βᴰ)
--       (λ _ _ → Cᴰ.rectify $ Cᴰ.≡out $ sym $ ueⱽ◁αⱽ.ηᴰ)
--     } where
--       module ueⱽ = UniversalElementⱽ ueⱽ
--       ueᴰ◁αⱽ = ueⱽ.toUniversalᴰ ◁PshIsoᴰ αⱽ
--       module Cᴰ = Fibers Cᴰ
--       module Qⱽ = PresheafⱽNotation Qⱽ
--       module ueⱽ◁αⱽ = UniversalElementᴰ ueᴰ◁αⱽ

-- module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {P : Presheaf C ℓP}
--   {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
--   {ue : UniversalElement C P}
--   where
--   _◁PshIsoᴰⱽ_ : (ueᴰ : UniversalElementᴰ Cᴰ ue Pᴰ) (αⱽ : PshIsoⱽ Pᴰ Qᴰ)
--     → UniversalElementᴰ Cᴰ ue Qᴰ
--   ueᴰ ◁PshIsoᴰⱽ αⱽ = record
--     { vertexᴰ = ueᴰ◁αⱽ.vertexᴰ
--     ; elementᴰ = ueᴰ◁αⱽ.elementᴰ
--     ; universalᴰ = isisoover
--       (λ p qᴰ → ueᴰ◁αⱽ.introᴰ qᴰ)
--       (λ p qᴰ → Qᴰ.rectify $ Qᴰ.≡out $ ueᴰ◁αⱽ.βᴰ)
--       (λ f fᴰ → Cᴰ.rectify $ Cᴰ.≡out $ sym $ ueᴰ◁αⱽ.ηᴰ)
--     } where
--       ueᴰ◁αⱽ = ueᴰ ◁PshIsoᴰ αⱽ
--       module Cᴰ = Fibers Cᴰ
--       module Qᴰ = PresheafᴰNotation Qᴰ
--       module ueᴰ◁αⱽ = UniversalElementᴰ ueᴰ◁αⱽ

-- open UniversalElement
-- module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {Q : Presheaf C ℓQ}
--   {ue : UniversalElement C Q}
--   {Pⱽ : Presheafⱽ (ue .vertex) Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
--   where
--   -- This could probably be implemented as a subst instead of manually.
--   _◁PshIsoⱽᴰ_ : UniversalElementⱽ Cᴰ (ue .vertex) Pⱽ
--     → PshIsoᴰ (yoRecIso ue) Pⱽ Qᴰ
--     → UniversalElementᴰ Cᴰ ue Qᴰ
--   ueⱽ ◁PshIsoⱽᴰ αᴰ = record
--     { vertexᴰ = ueⱽ.vertexⱽ
--     ; elementᴰ = Qᴰ.reind (Q.⋆IdL _) (αᴰ .fst .N-obᴰ ueⱽ.elementⱽ)
--     ; universalᴰ = isisoover
--       (λ q qᴰ → ueⱽ.introᴰ (αᴰ .snd .inv q qᴰ))
--       (λ q qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
--         Qᴰ.⟨⟩⋆⟨ (sym $ Qᴰ.reind-filler _ _) ∙ refl ⟩
--         ∙ (sym $ ∫α .trans .N-hom _ _ _ _)
--         ∙ cong (∫α .trans .N-ob _) ueⱽ.βᴰ
--         ∙ ∫α .nIso _ .snd .fst _)
--       (λ f fᴰ → Cᴰ.rectify $ Cᴰ.≡out $
--         ueⱽ.∫ue.intro≡ $
--           invPshIso ∫α .trans .N-hom _ _ _ _
--           ∙ Pⱽ.⟨⟩⋆⟨ cong (∫α .nIso _ .fst) (sym $ Qᴰ.reind-filler _ _)
--           ∙ ∫α .nIso _ .snd .snd _ ⟩)
--     } where
--       ∫α = ∫PshIso αᴰ
--       module ue = UniversalElementNotation ue
--       module ueⱽ = UniversalElementⱽ ueⱽ
--       module Q = PresheafNotation Q
--       module Qᴰ = PresheafᴰNotation Qᴰ
--       module Pⱽ = PresheafⱽNotation Pⱽ
--       module Cᴰ = Fibers Cᴰ
