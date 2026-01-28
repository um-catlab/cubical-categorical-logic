{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Constructions.ReindexFunctor.Base
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

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  where
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ
    ×ᴰ-π₁ : PshHomᴰ (π₁ P Q) (Pᴰ ×ᴰPsh Qᴰ) Pᴰ
    ×ᴰ-π₁ .N-obᴰ = fst
    ×ᴰ-π₁ .N-homᴰ = refl

    ×ᴰ-π₂ : PshHomᴰ (π₂ P Q) (Pᴰ ×ᴰPsh Qᴰ) Qᴰ
    ×ᴰ-π₂ .N-obᴰ = snd
    ×ᴰ-π₂ .N-homᴰ = refl

    module _ {R : Presheaf C ℓR}{Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ} where
      module _ {α : PshHom R P}{β : PshHom R Q} where
        ×ᴰ-introᴰ : PshHomᴰ α Rᴰ Pᴰ → PshHomᴰ β Rᴰ Qᴰ → PshHomᴰ (×PshIntro α β) Rᴰ (Pᴰ ×ᴰPsh Qᴰ)
        ×ᴰ-introᴰ αᴰ βᴰ .N-obᴰ rᴰ = αᴰ .N-obᴰ rᴰ , βᴰ .N-obᴰ rᴰ
        ×ᴰ-introᴰ αᴰ βᴰ .N-homᴰ = ΣPathP ((αᴰ .N-homᴰ) , (βᴰ .N-homᴰ))

      opaque
        ×ᴰ-UMPᴰ : IsoOver (×Psh-UMP P Q {R = R})
          (λ α → PshHomᴰ α Rᴰ (Pᴰ ×ᴰPsh Qᴰ))
          λ (α , β) → PshHomᴰ α Rᴰ Pᴰ × PshHomᴰ β Rᴰ Qᴰ
        ×ᴰ-UMPᴰ .IsoOver.fun α×β α×βᴰ = (α×βᴰ ⋆PshHomᴰ ×ᴰ-π₁) , (α×βᴰ ⋆PshHomᴰ ×ᴰ-π₂)
        ×ᴰ-UMPᴰ .IsoOver.inv (α , β) (αᴰ , βᴰ) = ×ᴰ-introᴰ αᴰ βᴰ
        ×ᴰ-UMPᴰ .IsoOver.rightInv (α , β) (αᴰ , βᴰ) =
          ΣPathP ((makePshHomᴰPathP _ _ _ (funExt (λ rᴰ → Pᴰ.rectify $ Pᴰ.≡out $ refl))) , (makePshHomᴰPathP _ _ _ (funExt (λ rᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl))))
        ×ᴰ-UMPᴰ .IsoOver.leftInv α×β α×βᴰ = makePshHomᴰPathP _ _ _ (funExt λ rᴰ → ΣPathP ((Pᴰ.rectify $ Pᴰ.≡out $ refl) , (Qᴰ.rectify $ Qᴰ.≡out $ refl)))

  module _ {P : Presheaf C ℓP}{Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
    where
    ×ⱽ-π₁ : PshHomⱽ (Pᴰ ×ⱽPsh Qᴰ) Pᴰ
    ×ⱽ-π₁ .N-obᴰ = fst
    ×ⱽ-π₁ .N-homᴰ = refl

    ×ⱽ-π₂ : PshHomⱽ (Pᴰ ×ⱽPsh Qᴰ) Qᴰ
    ×ⱽ-π₂ .N-obᴰ = snd
    ×ⱽ-π₂ .N-homᴰ = refl
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

    ×ⱽPsh-UMPᴰ : Iso (PshHomᴰ α Pᴰ Qᴰ × PshHomᴰ α Pᴰ Rᴰ) (PshHomᴰ α Pᴰ (Qᴰ ×ⱽPsh Rᴰ))
    ×ⱽPsh-UMPᴰ .Iso.fun αᴰβᴰ = ×ⱽ-introᴰ (αᴰβᴰ .fst) (αᴰβᴰ .snd)
    ×ⱽPsh-UMPᴰ .Iso.inv αᴰ = (αᴰ ⋆PshHomᴰⱽ ×ⱽ-π₁) , (αᴰ ⋆PshHomᴰⱽ ×ⱽ-π₂)
    ×ⱽPsh-UMPᴰ .Iso.sec αᴰ = makePshHomᴰPath (funExt λ p → refl)
    ×ⱽPsh-UMPᴰ .Iso.ret αᴰβᴰ = ΣPathP ((makePshHomᴰPath refl) , (makePshHomᴰPath refl))

  module _ {P : Presheaf C ℓP}{Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
    where
    ×ⱽ-introⱽ :
      PshHomⱽ Pᴰ Qᴰ
      → PshHomⱽ Pᴰ Rᴰ
      → PshHomⱽ Pᴰ (Qᴰ ×ⱽPsh Rᴰ)
    ×ⱽ-introⱽ = ×ⱽ-introᴰ

    ×ⱽPsh-UMPⱽ : Iso (PshHomⱽ Pᴰ Qᴰ × PshHomⱽ Pᴰ Rᴰ) (PshHomⱽ Pᴰ (Qᴰ ×ⱽPsh Rᴰ))
    ×ⱽPsh-UMPⱽ = ×ⱽPsh-UMPᴰ

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
  module _
    {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    {P : Presheaf C ℓP}{R : Presheaf D ℓR}
    {F : Functor D C}
    {α : PshHet F R P}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ R Dᴰ ℓRᴰ}
    (Fᴰ : Functorᴰ F Dᴰ Cᴰ)
    where
    ×ⱽ-introHet :
      PshHetᴰ α Fᴰ Rᴰ Pᴰ
      → PshHetᴰ α Fᴰ Rᴰ Qᴰ
      → PshHetᴰ α Fᴰ Rᴰ (Pᴰ ×ⱽPsh Qᴰ)
    ×ⱽ-introHet αᴰ βᴰ .N-obᴰ rᴰ = αᴰ .N-obᴰ rᴰ , βᴰ .N-obᴰ rᴰ
    ×ⱽ-introHet αᴰ βᴰ .N-homᴰ = ΣPathP (αᴰ .N-homᴰ , βᴰ .N-homᴰ)

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  where
  module _
    {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    {P : Presheaf C ℓP}
    {F : Functor D C}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
    (Fᴰ : Functorᴰ F Dᴰ Cᴰ)
    where
    reindPshᴰFunctor-×ⱽ :
      PshIsoⱽ (reindPshᴰFunctor Fᴰ (Pᴰ ×ⱽPsh Qᴰ))
              (reindPshᴰFunctor Fᴰ Pᴰ ×ⱽPsh reindPshᴰFunctor Fᴰ  Qᴰ)
    -- Forward direction can be defined using the UMP
    reindPshᴰFunctor-×ⱽ .fst = ×ⱽPsh-UMPᴰ .Iso.fun (reindPshᴰPshHomⱽ Fᴰ ×ⱽ-π₁ , reindPshᴰPshHomⱽ Fᴰ ×ⱽ-π₂)
    -- Backward direction must be defined manually
    reindPshᴰFunctor-×ⱽ .snd .inv p (pᴰ , qᴰ) = (pᴰ , qᴰ)
    reindPshᴰFunctor-×ⱽ .snd .rightInv = λ _ _ → refl
    reindPshᴰFunctor-×ⱽ .snd .leftInv = λ _ _ → refl

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
      (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler)
      , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler)

  -- This one is only Eq.refl on objects, would need a corresponding eqToPshIsoⱽ' like reindF''
  PshProdⱽ≅ᴰ :
    PshIsoⱽ (Pᴰ ×ᴰPsh Qᴰ) (reind (π₁ P Q) Pᴰ ×ⱽPsh reind (π₂ P Q) Qᴰ)
  PshProdⱽ≅ᴰ .fst .N-obᴰ x = x
  PshProdⱽ≅ᴰ .fst .N-homᴰ =
    ΣPathP ( (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler)
           , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler))
  PshProdⱽ≅ᴰ .snd .inv _ x = x
  PshProdⱽ≅ᴰ .snd .rightInv _ _ = refl
  PshProdⱽ≅ᴰ .snd .leftInv _ _ = refl

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (α : PshHom P Q)
  (Pᴰ : Presheafᴰ Q Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  -- This should work by a Yoneda argument...
  --   PshHomⱽ R (reind α (Pᴰ ×ⱽPsh Qᴰ))
  --   ≅ PshHomᴰ α R (Pᴰ ×ⱽPsh Qᴰ)
  --   ≅ (PshHomᴰ α R Pᴰ) × (PshHomᴰ α R Qᴰ)
  --   ≅ (PshHomⱽ R (reind α Pᴰ)) × (PshHomⱽ R (reind α Qᴰ))
  --   ≅ PshHomⱽ R ((reind α Pᴰ) ×ⱽPsh (reind α Qᴰ))
  reind×ⱽIsoⱽ : PshIsoⱽ (reind α (Pᴰ ×ⱽPsh Qᴰ)) (reind α Pᴰ ×ⱽPsh reind α Qᴰ)
  reind×ⱽIsoⱽ .fst = ×ⱽ-introⱽ (reind-introⱽ (reind-π ⋆PshHomᴰⱽ ×ⱽ-π₁)) (reind-introⱽ (reind-π ⋆PshHomᴰⱽ ×ⱽ-π₂))
  reind×ⱽIsoⱽ .snd .inv p = invers .N-obᴰ
    where
      invers : PshHomⱽ (reind α Pᴰ ×ⱽPsh reind α Qᴰ) (reind α (Pᴰ ×ⱽPsh Qᴰ))
      invers = reind-introⱽ (×ⱽ-introᴰ (×ⱽ-π₁ ⋆PshHomⱽᴰ reind-π) (×ⱽ-π₂ ⋆PshHomⱽᴰ reind-π))
  reind×ⱽIsoⱽ .snd .rightInv _ _ = refl
  reind×ⱽIsoⱽ .snd .leftInv _ _ = refl

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {x}
  {F : Functor C D}
  {Pᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓPᴰ}{Qᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ}
  where
  -- This is just the combination of the fact that ×ⱽPsh commutes with
  -- both kinds of reindexing. Maybe shouldn't even be a lemma
  reindⱽFunc×ⱽIsoⱽ :
    PshIsoⱽ (reindⱽFunc F (Pᴰ ×ⱽPsh Qᴰ))
            (reindⱽFunc F Pᴰ ×ⱽPsh reindⱽFunc F Qᴰ)
  reindⱽFunc×ⱽIsoⱽ =
    reindPshIsoⱽ (Functor→PshHet F x) (reindPshᴰFunctor-×ⱽ (π Dᴰ F))
    ⋆PshIsoⱽ reind×ⱽIsoⱽ (Functor→PshHet F x) (reindFunc F Pᴰ) (reindFunc F Qᴰ)

open PshSection
open Section
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {F : GlobalSection Cᴰ} where
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    (α : PshSection F Pᴰ)
    (β : PshSection F Qᴰ)
    where
    ×ᴰ-introS : PshSection F (Pᴰ ×ᴰPsh Qᴰ)
    ×ᴰ-introS .N-ob (p , q) = (α .N-ob p , β .N-ob q)
    ×ᴰ-introS .N-hom _ _ = ΣPathP (α .N-hom _ _ , β .N-hom _ _)
