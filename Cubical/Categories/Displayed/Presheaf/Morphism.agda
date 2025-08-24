{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf.Base

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ ℓQ ℓQᴰ ℓR ℓRᴰ : Level

open Functor
open Functorᴰ
open isIsoᴰ
open isIsoOver


module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHom P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  record PshHomᴰ : Type (ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓP $ ℓ-max ℓCᴰ' $ ℓ-max ℓCᴰ $ ℓ-max ℓC' $ ℓ-max ℓC $ ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓP $ ℓ-max ℓCᴰ $ ℓC) where
    no-eta-equality
    field
      N-obᴰ  : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α .fst x p ][ xᴰ ]
      N-homᴰ :
        ∀ {x y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}
        → {f : C [ x , y ]}{p : P.p[ y ]}
        → {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : Pᴰ.p[ p ][ yᴰ ]}
        → N-obᴰ (fᴰ Pᴰ.⋆ᴰ pᴰ)
            Qᴰ.≡[ α .snd x y f p ]
          (fᴰ Qᴰ.⋆ᴰ N-obᴰ pᴰ)

    ∫PshHomᴰ : PshHom (∫P Pᴰ) (∫P Qᴰ)
    ∫PshHomᴰ .fst (x , xᴰ) (p , pᴰ) = (α .fst _ p) , (N-obᴰ pᴰ)
    ∫PshHomᴰ .snd _ _ (f , fᴰ) (p , pᴰ) = ΣPathP ((α .snd _ _ f p) , N-homᴰ)

    private
      module ∫Pᴰ = PresheafNotation (∫P Pᴰ)
      module ∫Qᴰ = PresheafNotation (∫P Qᴰ)

    N-obᴰ⟨_⟩ :
      ∀ {xxᴰ}{ppᴰ ppᴰ'}
      → Path ∫Pᴰ.p[ xxᴰ ] ppᴰ ppᴰ'
      → Path ∫Qᴰ.p[ xxᴰ ] (_ , N-obᴰ (ppᴰ .snd)) (_ , N-obᴰ (ppᴰ' .snd))
    N-obᴰ⟨_⟩ = cong (∫PshHomᴰ .fst _)

  isPshIsoᴰ : PshHomᴰ → isPshIso {P = P}{Q = Q} α → Type _
  isPshIsoᴰ αᴰ αIsIso = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
      → isIsoOver (isIsoToIso (αIsIso x)) Pᴰ.p[_][ xᴰ ] Qᴰ.p[_][ xᴰ ]
          (λ _ → αᴰ .PshHomᴰ.N-obᴰ)

  isPshEquivOver : PshHomᴰ → Type _
  isPshEquivOver αᴰ = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
    → isEquivOver {P = Pᴰ.p[_][ xᴰ ]}{Q = Qᴰ.p[_][ xᴰ ]}{f = α .fst x}
        λ _ → αᴰ .PshHomᴰ.N-obᴰ

open PshHomᴰ
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshIso P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  PshIsoᴰ : Type _
  PshIsoᴰ =
    Σ[ αᴰ ∈ PshHomᴰ (α .fst) Pᴰ Qᴰ ] isPshIsoᴰ (α .fst) Pᴰ Qᴰ αᴰ (α .snd)
  open IsoOver
  mkPshIsoᴰEquivOver : ∀ (αᴰ : PshHomᴰ (α .fst) Pᴰ Qᴰ)
    → isPshEquivOver (α .fst) Pᴰ Qᴰ αᴰ
    → PshIsoᴰ
  mkPshIsoᴰEquivOver αᴰ isPshEqv .fst = αᴰ
  mkPshIsoᴰEquivOver αᴰ isPshEqv .snd {x}{xᴰ} =
    isisoover (α-isoOver .inv) (α-isoOver .rightInv)
      λ p pᴰ → Pᴰ.rectify $ α-isoOver .leftInv p pᴰ
    where
    α-isoOver = equivOver→IsoOver {P = Pᴰ.p[_][ xᴰ ]}{Q = Qᴰ.p[_][ xᴰ ]}
                  (isoToEquiv (isIsoToIso (α .snd x)))
      (λ a → αᴰ .PshHomᴰ.N-obᴰ)
      isPshEqv

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {α : PshIso P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ} where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  ∫PshIsoᴰ : PshIsoᴰ α Pᴰ Qᴰ → PshIso (∫P Pᴰ) (∫P Qᴰ)
  ∫PshIsoᴰ (αᴰ , αᴰIsPshIsoᴰ) .fst = PshHomᴰ.∫PshHomᴰ αᴰ
  ∫PshIsoᴰ (αᴰ , αᴰIsPshIsoᴰ) .snd (x , xᴰ) .fst (q , qᴰ) = _ , αᴰIsPshIsoᴰ .inv q qᴰ
  ∫PshIsoᴰ (αᴰ , αᴰIsPshIsoᴰ) .snd (x , xᴰ) .snd .fst (q , qᴰ) =
    ΣPathP (_ , αᴰIsPshIsoᴰ .rightInv q qᴰ)
  ∫PshIsoᴰ (αᴰ , αᴰIsPshIsoᴰ) .snd (x , xᴰ) .snd .snd (p , pᴰ) =
    ΣPathP (_ , αᴰIsPshIsoᴰ .leftInv p pᴰ)

-- Vertical PshHom/Iso are the ones over idPshHom/idPshIso. They need
-- special composition operators to package up the reindexing.
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
  PshHomⱽ : Type _
  PshHomⱽ = PshHomᴰ idPshHom Pᴰ Qᴰ
  PshIsoⱽ : Type _
  PshIsoⱽ = PshIsoᴰ idPshIso Pᴰ Qᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  where
  idPshHomᴰ : PshHomⱽ Pᴰ Pᴰ
  idPshHomᴰ .N-obᴰ = λ z → z
  idPshHomᴰ .N-homᴰ = refl

  idPshIsoᴰ : PshIsoⱽ Pᴰ Pᴰ
  idPshIsoᴰ .fst = idPshHomᴰ
  idPshIsoᴰ .snd .inv = λ _ z → z
  idPshIsoᴰ .snd .rightInv = λ _ _ → refl
  idPshIsoᴰ .snd .leftInv = λ _ _ → refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ

  module _ {α : PshHom P Q}{β : PshHom Q R} where
    _⋆PshHomᴰ_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ)(βᴰ : PshHomᴰ β Qᴰ Rᴰ) → PshHomᴰ (α ⋆PshHom β) Pᴰ Rᴰ
    (αᴰ ⋆PshHomᴰ βᴰ) = record
      { N-obᴰ = λ pᴰ → ∫⋆ .fst _ (_ , pᴰ) .snd
      ; N-homᴰ = Rᴰ.rectify $ Rᴰ.≡out $ ∫⋆ .snd _ _ _ _
      } where
        ∫⋆ = ∫PshHomᴰ αᴰ ⋆PshHom ∫PshHomᴰ βᴰ

  module _ {α : PshIso P Q}{β : PshIso Q R} where
    _⋆PshIsoᴰ_ : (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)(βᴰ : PshIsoᴰ β Qᴰ Rᴰ) → PshIsoᴰ (α ⋆PshIso β) Pᴰ Rᴰ
    (αᴰ ⋆PshIsoᴰ βᴰ) = (αᴰ .fst ⋆PshHomᴰ βᴰ .fst) ,
      isisoover
        (λ r rᴰ → ∫⋆ .snd _ .fst (r , rᴰ) .snd)
        (λ r rᴰ → Rᴰ.rectify $ Rᴰ.≡out $ ∫⋆ .snd _ .snd .fst (r , rᴰ))
        (λ p pᴰ → Pᴰ.rectify $ Pᴰ.≡out $ ∫⋆ .snd _ .snd .snd (p , pᴰ))
      where
        module Pᴰ = PresheafᴰNotation Pᴰ
        ∫⋆ = ∫PshIsoᴰ αᴰ ⋆PshIso ∫PshIsoᴰ βᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  module _ {α : PshIso P Q} where
    invPshIsoᴰ : PshIsoᴰ α Pᴰ Qᴰ → PshIsoᴰ (invPshIso α) Qᴰ Pᴰ
    invPshIsoᴰ αᴰ = record
      { N-obᴰ = αᴰ .snd .inv _
      ; N-homᴰ = Pᴰ.rectify $ Pᴰ.≡out $ ∫αᴰ⁻ .fst .snd _ _ _ _
      }
      , isisoover (λ a → αᴰ .fst .N-obᴰ) (αᴰ .snd .leftInv) (αᴰ .snd .rightInv)
      where
        module Pᴰ = PresheafᴰNotation Pᴰ
        ∫αᴰ⁻ = invPshIso (∫PshIsoᴰ αᴰ)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
  where
  invPshIsoⱽ : PshIsoⱽ Pᴰ Qᴰ → PshIsoⱽ Qᴰ Pᴰ
  invPshIsoⱽ αⱽ = record
    { N-obᴰ = αⱽ⁻ .fst .N-obᴰ
    ; N-homᴰ = Pᴰ.rectify $ αⱽ⁻ .fst .N-homᴰ
    } , (isisoover
      (αⱽ⁻ .snd .inv)
      (αⱽ⁻ .snd .rightInv)
      (αⱽ⁻ .snd .leftInv))
    where
      module Pᴰ = PresheafᴰNotation Pᴰ
      αⱽ⁻ = invPshIsoᴰ αⱽ

-- The variants of these are all just eta expansions. We could do
-- something like reindF' but I'll just copy/paste for today.
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ
  _⋆PshHomⱽ_ : (αᴰ : PshHomⱽ Pᴰ Qᴰ)(βᴰ : PshHomⱽ Qᴰ Rᴰ) → PshHomⱽ Pᴰ Rᴰ
  αᴰ ⋆PshHomⱽ βᴰ = record { N-obᴰ = αᴰ⋆ᴰβᴰ .N-obᴰ ; N-homᴰ = Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .N-homᴰ }
    where
      αᴰ⋆ᴰβᴰ = αᴰ ⋆PshHomᴰ βᴰ

  _⋆PshIsoⱽ_ : (αᴰ : PshIsoⱽ Pᴰ Qᴰ)(βᴰ : PshIsoⱽ Qᴰ Rᴰ) → PshIsoⱽ Pᴰ Rᴰ
  αᴰ ⋆PshIsoⱽ βᴰ = (αᴰ .fst ⋆PshHomⱽ βᴰ .fst)
    , (isisoover (αᴰ⋆ᴰβᴰ .snd .inv)
                 (λ _ _ → Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .rightInv _ _)
                 (λ _ _ → Pᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .leftInv _ _))
    where
      αᴰ⋆ᴰβᴰ = αᴰ ⋆PshIsoᴰ βᴰ
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ
  module _ {α : PshHom P Q} where
    _⋆PshHomᴰⱽ_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ)(βᴰ : PshHomⱽ Qᴰ Rᴰ) → PshHomᴰ α Pᴰ Rᴰ
    αᴰ ⋆PshHomᴰⱽ βᴰ = record { N-obᴰ = αᴰ⋆ᴰβᴰ .N-obᴰ ; N-homᴰ = Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .N-homᴰ }
      where
        αᴰ⋆ᴰβᴰ = αᴰ ⋆PshHomᴰ βᴰ

  module _ {α : PshIso P Q} where
    _⋆PshIsoᴰⱽ_ : (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)(βᴰ : PshIsoⱽ Qᴰ Rᴰ) → PshIsoᴰ α Pᴰ Rᴰ
    αᴰ ⋆PshIsoᴰⱽ βᴰ = (αᴰ .fst ⋆PshHomᴰⱽ βᴰ .fst)
      , (isisoover (αᴰ⋆ᴰβᴰ .snd .inv)
                   (λ _ _ → Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .rightInv _ _)
                   (λ _ _ → Pᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .leftInv _ _))
      where
        αᴰ⋆ᴰβᴰ = αᴰ ⋆PshIsoᴰ βᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ
  module _ {β : PshHom P R} where
    _⋆PshHomⱽᴰ_ : (αᴰ : PshHomⱽ Pᴰ Qᴰ)(βᴰ : PshHomᴰ β Qᴰ Rᴰ) → PshHomᴰ β Pᴰ Rᴰ
    αᴰ ⋆PshHomⱽᴰ βᴰ = record { N-obᴰ = αᴰ⋆ᴰβᴰ .N-obᴰ ; N-homᴰ = Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .N-homᴰ }
      where
        αᴰ⋆ᴰβᴰ = αᴰ ⋆PshHomᴰ βᴰ

  module _ {β : PshIso P R} where
    _⋆PshIsoⱽᴰ_ : (αᴰ : PshIsoⱽ Pᴰ Qᴰ)(βᴰ : PshIsoᴰ β Qᴰ Rᴰ) → PshIsoᴰ β Pᴰ Rᴰ
    αᴰ ⋆PshIsoⱽᴰ βᴰ = (αᴰ .fst ⋆PshHomⱽᴰ βᴰ .fst)
      , (isisoover (αᴰ⋆ᴰβᴰ .snd .inv)
                   (λ _ _ → Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .rightInv _ _)
                   (λ _ _ → Pᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .leftInv _ _))
      where
        αᴰ⋆ᴰβᴰ = αᴰ ⋆PshIsoᴰ βᴰ

-- We can use paths if the presheaves are of the same level
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓP}
  (α : PshIso P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  module _ (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) {x : C.ob} where
    private
      α⟨x⟩ : CatIso (SET ℓP) (P .F-ob x) (Q .F-ob x)
      α⟨x⟩ = PshIso→SETIso P Q α x
    PshIsoᴰ→SETᴰIsoᴰ : ∀ xᴰ → CatIsoᴰ (SETᴰ ℓP ℓPᴰ) α⟨x⟩ (Pᴰ .F-obᴰ xᴰ) (Qᴰ .F-obᴰ xᴰ)
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .fst p pᴰ = αᴰ .fst .N-obᴰ pᴰ
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .snd .invᴰ q qᴰ = αᴰ .snd .inv q qᴰ
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .snd .secᴰ = funExt λ q → funExt λ qᴰ →
      αᴰ .snd .rightInv q qᴰ
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .snd .retᴰ = funExt λ p → funExt λ pᴰ →
      αᴰ .snd .leftInv p pᴰ

  PshIsoᴰ→PathP
      : ∀ (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)
      → PathP (λ i → Presheafᴰ (PshIso→Path P Q α i) Cᴰ ℓPᴰ) Pᴰ Qᴰ
  PshIsoᴰ→PathP αᴰ =
    Functorᴰ≡
      (λ xᴰ → CatIsoᴰ→P≡Q (PshIso→SETIso P Q α _) (PshIsoᴰ→SETᴰIsoᴰ αᴰ xᴰ))
      λ {x = x}{xᴰ = xᴰ} fᴰ →
        toPathP (funExt (λ q → funExt (λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
          sym (Qᴰ.reind-filler _ _)
          ∙ cong (∫αᴰ .fst .fst _) Pᴰ.⟨ refl ⟩⋆⟨ (sym $ Pᴰ.reind-filler _ _) ⟩
          ∙ ∫αᴰ .fst .snd _ _ _ _
          ∙ Qᴰ.⟨ refl ⟩⋆⟨ cong (∫αᴰ .fst .fst _) (cong (∫αᴰ .snd _ .fst) (sym $ Qᴰ.reind-filler _ _))
                 ∙ ∫αᴰ .snd _ .snd .fst _ ⟩
        )))
    where
      ∫αᴰ : PshIso (∫P Pᴰ) (∫P Qᴰ)
      ∫αᴰ = ∫PshIsoᴰ αᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ} where
  pathToPshIsoⱽ : Pᴰ ≡ Qᴰ → PshIsoⱽ Pᴰ Qᴰ
  pathToPshIsoⱽ = J (λ Qᴰ _ → PshIsoⱽ Pᴰ Qᴰ) idPshIsoᴰ
