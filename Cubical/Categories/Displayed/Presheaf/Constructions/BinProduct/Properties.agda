{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Bifunctorᴰ
open Functorᴰ

open isIsoOver

open PshHomᴰ
open PshHom
open PshIso

-- Product
module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  where
  module _ {P : Presheaf C ℓP}{Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
    where
    ×ⱽ-introⱽ :
      PshHomⱽ Pᴰ Qᴰ
      → PshHomⱽ Pᴰ Rᴰ
      → PshHomⱽ Pᴰ (Qᴰ ×ⱽPsh Rᴰ)
    ×ⱽ-introⱽ αⱽ βⱽ .N-obᴰ = λ z → αⱽ .N-obᴰ z , βⱽ .N-obᴰ z
    ×ⱽ-introⱽ αⱽ βⱽ .N-homᴰ = ΣPathP ((αⱽ .N-homᴰ) , (βⱽ .N-homᴰ))

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {α : PshHom P Q}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ}
    where
    ×ⱽ-introᴰ :
      PshHomᴰ α Pᴰ Qᴰ
      → PshHomᴰ α Pᴰ Rᴰ
      → PshHomᴰ α Pᴰ (Qᴰ ×ⱽPsh Rᴰ)
    ×ⱽ-introᴰ αᴰ βᴰ .N-obᴰ = λ z → αᴰ .N-obᴰ z , βᴰ .N-obᴰ z
    ×ⱽ-introᴰ αᴰ βᴰ .N-homᴰ = ΣPathP ((αᴰ .N-homᴰ) , (βᴰ .N-homᴰ))

  module _ {P : Presheaf C ℓP}{Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
    where
    ×ⱽ-π₁ : PshHomⱽ (Pᴰ ×ⱽPsh Qᴰ) Pᴰ
    ×ⱽ-π₁ .N-obᴰ = fst
    ×ⱽ-π₁ .N-homᴰ = refl

    ×ⱽ-π₂ : PshHomⱽ (Pᴰ ×ⱽPsh Qᴰ) Qᴰ
    ×ⱽ-π₂ .N-obᴰ = snd
    ×ⱽ-π₂ .N-homᴰ = refl

  -- This is like PshProdⱽ .F-hom but for homomorphisms/isomorphisms
  -- between presheaves of different levels
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    {Qᴰ' : Presheafᴰ Q Cᴰ ℓQᴰ'}
    where
    module _ {α : PshHom P Q} where
      _×ⱽHom_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ) (βᴰ : PshHomᴰ α Pᴰ' Qᴰ')
        → PshHomᴰ α (Pᴰ ×ⱽPsh Pᴰ') (Qᴰ ×ⱽPsh Qᴰ')
      (αᴰ ×ⱽHom βᴰ) = ×ⱽ-introᴰ (×ⱽ-π₁ ⋆PshHomⱽᴰ αᴰ) (×ⱽ-π₂ ⋆PshHomⱽᴰ βᴰ)

    module _ {α : PshIso P Q} where
      _×ⱽIso_ : (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) (βᴰ : PshIsoᴰ α Pᴰ' Qᴰ')
        → PshIsoᴰ α (Pᴰ ×ⱽPsh Pᴰ') (Qᴰ ×ⱽPsh Qᴰ')
      (αᴰ ×ⱽIso βᴰ) .fst = (αᴰ .fst) ×ⱽHom (βᴰ .fst)
      (αᴰ ×ⱽIso βᴰ) .snd .inv _ = invers .N-obᴰ where
        invers : PshHomᴰ (invPshIso α .trans) (Qᴰ ×ⱽPsh Qᴰ') (Pᴰ ×ⱽPsh Pᴰ')
        invers = ×ⱽ-introᴰ (×ⱽ-π₁ ⋆PshHomⱽᴰ (invPshIsoᴰ αᴰ .fst)) (×ⱽ-π₂ ⋆PshHomⱽᴰ (invPshIsoᴰ βᴰ .fst))
      (αᴰ ×ⱽIso βᴰ) .snd .rightInv _ _ = ΣPathP ((αᴰ .snd .rightInv _ _) , (βᴰ .snd .rightInv _ _))
      (αᴰ ×ⱽIso βᴰ) .snd .leftInv _ _ = ΣPathP ((αᴰ .snd .leftInv _ _) , (βᴰ .snd .leftInv _ _))

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  PshProdⱽ≡ᴰ :
    Pᴰ ×ᴰPsh Qᴰ ≡ reind (π₁ P Q) Pᴰ ×ⱽPsh reind (π₂ P Q) Qᴰ
  PshProdⱽ≡ᴰ = Functorᴰ≡
    (λ Aᴰ → funExt λ (p , q) → ΣPathPProp (λ _ → isPropIsSet) refl)
    λ fᴰ → funExt λ (p , q) → funExt λ (pᴰ , qᴰ) → ΣPathP $
      (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)
      , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _)

  -- This one is only Eq.refl on objects, would need a corresponding eqToPshIsoⱽ' like reindF''
  PshProdⱽ≅ᴰ :
    PshIsoⱽ (Pᴰ ×ᴰPsh Qᴰ) (reind (π₁ P Q) Pᴰ ×ⱽPsh reind (π₂ P Q) Qᴰ)
  PshProdⱽ≅ᴰ .fst .N-obᴰ x = x
  PshProdⱽ≅ᴰ .fst .N-homᴰ =
    ΣPathP ( (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)
           , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _))
  PshProdⱽ≅ᴰ .snd .inv _ x = x
  PshProdⱽ≅ᴰ .snd .rightInv _ _ = refl
  PshProdⱽ≅ᴰ .snd .leftInv _ _ = refl

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {α : PshHom P Q}
  where
  reind×ⱽIsoⱽ : PshIsoⱽ (reind α (Pᴰ ×ⱽPsh Qᴰ)) (reind α Pᴰ ×ⱽPsh reind α Qᴰ)
  reind×ⱽIsoⱽ .fst = ×ⱽ-introⱽ (reind-introⱽ (reind-π ⋆PshHomᴰⱽ ×ⱽ-π₁)) (reind-introⱽ (reind-π ⋆PshHomᴰⱽ ×ⱽ-π₂))
  reind×ⱽIsoⱽ .snd .inv p = invers .N-obᴰ
    where
      invers : PshHomⱽ (reind α Pᴰ ×ⱽPsh reind α Qᴰ) (reind α (Pᴰ ×ⱽPsh Qᴰ))
      invers = reind-introⱽ (×ⱽ-introᴰ (×ⱽ-π₁ ⋆PshHomⱽᴰ reind-π) (×ⱽ-π₂ ⋆PshHomⱽᴰ reind-π))
  reind×ⱽIsoⱽ .snd .rightInv _ _ = refl
  reind×ⱽIsoⱽ .snd .leftInv _ _ = refl

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf D ℓP}
  {Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Dᴰ ℓQᴰ}
  {F : Functor C D}
  where
  reindFunc×ⱽIsoⱽ :
    PshIsoⱽ (reindFunc F (Pᴰ ×ⱽPsh Qᴰ))
            (reindFunc F Pᴰ ×ⱽPsh reindFunc F Qᴰ)
  reindFunc×ⱽIsoⱽ = eqToPshIsoⱽ the-eq where
    the-eq : PresheafᴰEq (reindFunc F (Pᴰ ×ⱽPsh Qᴰ)) (reindFunc F Pᴰ ×ⱽPsh reindFunc F Qᴰ)
    the-eq = (Eq.refl , Eq.refl)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {x}
  {F : Functor C D}
  {Pᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓPᴰ}{Qᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ}
  where
  reindⱽFunc×ⱽIsoⱽ :
    PshIsoⱽ (reindⱽFunc F (Pᴰ ×ⱽPsh Qᴰ))
            (reindⱽFunc F Pᴰ ×ⱽPsh reindⱽFunc F Qᴰ)
  reindⱽFunc×ⱽIsoⱽ =
    reindPshIsoⱽ reindFunc×ⱽIsoⱽ
    ⋆PshIsoⱽ reind×ⱽIsoⱽ
