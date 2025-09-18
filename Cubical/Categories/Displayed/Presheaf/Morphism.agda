{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Base

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓR ℓRᴰ : Level

open Functor
open Functorᴰ
open isIsoᴰ
open isIsoOver
open PshHom
open PshIso

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
      N-obᴰ  : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α .N-ob x p ][ xᴰ ]
      N-homᴰ :
        ∀ {x y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}
        → {f : C [ x , y ]}{p : P.p[ y ]}
        → {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : Pᴰ.p[ p ][ yᴰ ]}
        → N-obᴰ (fᴰ Pᴰ.⋆ᴰ pᴰ)
            Qᴰ.≡[ α .N-hom x y f p ]
          (fᴰ Qᴰ.⋆ᴰ N-obᴰ pᴰ)

    ∫PshHom : PshHom (∫P Pᴰ) (∫P Qᴰ)
    ∫PshHom .N-ob (x , xᴰ) (p , pᴰ) = (α .N-ob _ p) , (N-obᴰ pᴰ)
    ∫PshHom .N-hom _ _ (f , fᴰ) (p , pᴰ) = ΣPathP ((α .N-hom _ _ f p) , N-homᴰ)

    private
      module ∫Pᴰ = PresheafNotation (∫P Pᴰ)
      module ∫Qᴰ = PresheafNotation (∫P Qᴰ)

    N-obᴰ⟨_⟩ :
      ∀ {xxᴰ}{ppᴰ ppᴰ'}
      → Path ∫Pᴰ.p[ xxᴰ ] ppᴰ ppᴰ'
      → Path ∫Qᴰ.p[ xxᴰ ] (_ , N-obᴰ (ppᴰ .snd)) (_ , N-obᴰ (ppᴰ' .snd))
    N-obᴰ⟨_⟩ = cong (∫PshHom .N-ob _)

  isPshIsoᴰ : PshHomᴰ → isPshIso {P = P}{Q = Q} α → Type _
  isPshIsoᴰ αᴰ αIsIso = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
      → isIsoOver (isIsoToIso (αIsIso x)) Pᴰ.p[_][ xᴰ ] Qᴰ.p[_][ xᴰ ]
          (λ _ → αᴰ .PshHomᴰ.N-obᴰ)

  isPshEquivOver : PshHomᴰ → Type _
  isPshEquivOver αᴰ = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
    → isEquivOver {P = Pᴰ.p[_][ xᴰ ]}{Q = Qᴰ.p[_][ xᴰ ]}{f = α .N-ob x}
        λ _ → αᴰ .PshHomᴰ.N-obᴰ

open PshHomᴰ

-- A displayed "heteromorphism" is a kind of morphism between
-- displayed presheaves on different categories.
module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf D ℓQ}
  {F : Functor C D}
  (α : PshHet F P Q)
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ) where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  PshHetᴰ : Type _
  PshHetᴰ = PshHomᴰ α Pᴰ (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {x}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  xᴰ
  where
  Functorᴰ→PshHetᴰ : PshHetᴰ (Functor→PshHet F x) Fᴰ (Cᴰ [-][-, xᴰ ]) (Dᴰ [-][-, Fᴰ .F-obᴰ xᴰ ])
  Functorᴰ→PshHetᴰ .N-obᴰ = Fᴰ .F-homᴰ
  Functorᴰ→PshHetᴰ .N-homᴰ = Fᴰ .F-seqᴰ _ _

-- A "vertical" heteromorphism is between objects
module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {x}
  {F : Functor C D}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ)
  (Qⱽ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ) where

  PshHetⱽ : Type _
  PshHetⱽ = PshHetᴰ (Functor→PshHet F x) Fᴰ Pⱽ Qⱽ

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

  -- TODO make this a record
  PshIsoᴰ : Type _
  PshIsoᴰ =
    Σ[ αᴰ ∈ PshHomᴰ (α .trans) Pᴰ Qᴰ ]
      isPshIsoᴰ (α .trans) Pᴰ Qᴰ αᴰ (α .nIso)
  open IsoOver
  mkPshIsoᴰEquivOver : ∀ (αᴰ : PshHomᴰ (α .trans) Pᴰ Qᴰ)
    → isPshEquivOver (α .trans) Pᴰ Qᴰ αᴰ
    → PshIsoᴰ
  mkPshIsoᴰEquivOver αᴰ isPshEqv .fst = αᴰ
  mkPshIsoᴰEquivOver αᴰ isPshEqv .snd {x}{xᴰ} =
    isisoover (α-isoOver .inv) (α-isoOver .rightInv)
      λ p pᴰ → Pᴰ.rectify $ α-isoOver .leftInv p pᴰ
    where
    α-isoOver = equivOver→IsoOver {P = Pᴰ.p[_][ xᴰ ]}{Q = Qᴰ.p[_][ xᴰ ]}
                  (isoToEquiv (isIsoToIso (α .nIso x)))
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
  ∫PshIso : PshIsoᴰ α Pᴰ Qᴰ → PshIso (∫P Pᴰ) (∫P Qᴰ)
  ∫PshIso (αᴰ , αᴰIsPshIsoᴰ) .trans = PshHomᴰ.∫PshHom αᴰ
  ∫PshIso (αᴰ , αᴰIsPshIsoᴰ) .nIso (x , xᴰ) .fst (q , qᴰ) = _ , αᴰIsPshIsoᴰ .inv q qᴰ
  ∫PshIso (αᴰ , αᴰIsPshIsoᴰ) .nIso (x , xᴰ) .snd .fst (q , qᴰ) =
    ΣPathP (_ , αᴰIsPshIsoᴰ .rightInv q qᴰ)
  ∫PshIso (αᴰ , αᴰIsPshIsoᴰ) .nIso (x , xᴰ) .snd .snd (p , pᴰ) =
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
  {Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ} where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    fun-ty = Eq.singl {A = ∀ {x} → P.p[ x ] → (xᴰ : Cᴰ.ob[ x ]) → Type ℓPᴰ} Pᴰ.p[_][_]
    hom-ty : fun-ty → Type _
    hom-ty singl-fun =
      Eq.singlP (Eq.ap (λ p[_][_] → {x y : Category.ob C}{f : C [ y , x ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
       {p : P.p[ x ]} →
      Cᴰ [ f ][ yᴰ , xᴰ ] → p[ p ][ xᴰ ] → p[ f P.⋆ p ][ yᴰ ]) (singl-fun .snd))
      Pᴰ._⋆ᴰ_
  module _ where
    eqToPshIso-obᴰ : ((p[_][_] , _) : fun-ty) → ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]}
      → Pᴰ.p[ p ][ xᴰ ] → p[ p ][ xᴰ ]
    eqToPshIso-obᴰ (_ , Eq.refl) = λ z → z

    eqToPshIso-invᴰ : ((p[_][_] , _) : fun-ty) → ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]}
      → p[ p ][ xᴰ ] → Pᴰ.p[ p ][ xᴰ ]
    eqToPshIso-invᴰ (_ , Eq.refl) = λ z → z

    eqToPshIso-homᴰ : ∀ ((p[_][_] , p≡Pp) : fun-ty) ((_⋆ᴰ_ , _) : hom-ty (p[_][_] , p≡Pp))
      {x}{y}{xᴰ}{yᴰ}{f : C [ x , y ]}{p : P.p[ y ]} →
      {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]} {pᴰ : Pᴰ.p[ p ][ yᴰ ]}
      → eqToPshIso-obᴰ (p[_][_] , p≡Pp) (fᴰ Pᴰ.⋆ᴰ pᴰ)
        ≡ (fᴰ ⋆ᴰ eqToPshIso-obᴰ (p[_][_] , p≡Pp) pᴰ)
    eqToPshIso-homᴰ (_ , Eq.refl) (_ , Eq.refl) = refl

    eqToPshIso-rightInv : ∀ ((p[_][_] , p≡Pp) : fun-ty) ((_⋆ᴰ_ , _) : hom-ty (p[_][_] , p≡Pp))
      → ∀ {x}{xᴰ}{p : P.p[ x ]}{qᴰ : p[ p ][ xᴰ ]}
      → eqToPshIso-obᴰ (p[_][_] , p≡Pp)
      (eqToPshIso-invᴰ (p[_][_] , p≡Pp) qᴰ)
      ≡ qᴰ
    eqToPshIso-rightInv (_ , Eq.refl) (_ , Eq.refl) = refl

    eqToPshIso-leftInv : ∀ ((p[_][_] , p≡Pp) : fun-ty) ((_⋆ᴰ_ , _) : hom-ty (p[_][_] , p≡Pp))
      → ∀ {x}{xᴰ}{p : P.p[ x ]}{pᴰ : Pᴰ.p[ p ][ xᴰ ]}
      → eqToPshIso-invᴰ (p[_][_] , p≡Pp) (eqToPshIso-obᴰ (p[_][_] , p≡Pp) pᴰ)
        ≡ pᴰ
    eqToPshIso-leftInv (_ , Eq.refl) (_ , Eq.refl) = refl

  eqToPshHomⱽ : PresheafᴰEq Pᴰ Qᴰ → PshHomⱽ Pᴰ Qᴰ
  eqToPshHomⱽ Pᴰ≡Qᴰ .N-obᴰ = eqToPshIso-obᴰ (_ , Pᴰ≡Qᴰ .fst)
  eqToPshHomⱽ Pᴰ≡Qᴰ .N-homᴰ = eqToPshIso-homᴰ (_ , Pᴰ≡Qᴰ .fst) (_ , Pᴰ≡Qᴰ .snd)

  eqToPshIsoⱽ : PresheafᴰEq Pᴰ Qᴰ → PshIsoⱽ Pᴰ Qᴰ
  eqToPshIsoⱽ Pᴰ≡Qᴰ .fst = eqToPshHomⱽ Pᴰ≡Qᴰ
  eqToPshIsoⱽ Pᴰ≡Qᴰ .snd .inv p = eqToPshIso-invᴰ (_ , Pᴰ≡Qᴰ .fst)
  eqToPshIsoⱽ Pᴰ≡Qᴰ .snd .rightInv p qᴰ = eqToPshIso-rightInv (_ , Pᴰ≡Qᴰ .fst) (_ , Pᴰ≡Qᴰ .snd)
  eqToPshIsoⱽ Pᴰ≡Qᴰ .snd .leftInv p pᴰ = eqToPshIso-leftInv (_ , Pᴰ≡Qᴰ .fst) (_ , Pᴰ≡Qᴰ .snd)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  where
  idPshIsoᴰ : PshIsoⱽ Pᴰ Pᴰ
  idPshIsoᴰ = eqToPshIsoⱽ (Eq.refl , Eq.refl)

  idPshHomᴰ : PshHomⱽ Pᴰ Pᴰ
  idPshHomᴰ = idPshIsoᴰ .fst

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ} where
  pathToPshIsoⱽ : Pᴰ ≡ Qᴰ → PshIsoⱽ Pᴰ Qᴰ
  pathToPshIsoⱽ = J (λ Qᴰ _ → PshIsoⱽ Pᴰ Qᴰ) idPshIsoᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ

  module _ {α : PshHom P Q}{β : PshHom Q R} where
    _⋆PshHomᴰ_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ)(βᴰ : PshHomᴰ β Qᴰ Rᴰ) → PshHomᴰ (α ⋆PshHom β) Pᴰ Rᴰ
    (αᴰ ⋆PshHomᴰ βᴰ) = record
      { N-obᴰ = λ pᴰ → ∫⋆ .N-ob _ (_ , pᴰ) .snd
      ; N-homᴰ = Rᴰ.rectify $ Rᴰ.≡out $ ∫⋆ .N-hom _ _ _ _
      } where
        ∫⋆ = ∫PshHom αᴰ ⋆PshHom ∫PshHom βᴰ

  module _ {α : PshIso P Q}{β : PshIso Q R} where
    _⋆PshIsoᴰ_ : (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)(βᴰ : PshIsoᴰ β Qᴰ Rᴰ) → PshIsoᴰ (α ⋆PshIso β) Pᴰ Rᴰ
    (αᴰ ⋆PshIsoᴰ βᴰ) = (αᴰ .fst ⋆PshHomᴰ βᴰ .fst) ,
      isisoover
        (λ r rᴰ → ∫⋆ .nIso _ .fst (r , rᴰ) .snd)
        (λ r rᴰ → Rᴰ.rectify $ Rᴰ.≡out $ ∫⋆ .nIso _ .snd .fst (r , rᴰ))
        (λ p pᴰ → Pᴰ.rectify $ Pᴰ.≡out $ ∫⋆ .nIso _ .snd .snd (p , pᴰ))
      where
        module Pᴰ = PresheafᴰNotation Pᴰ
        ∫⋆ = ∫PshIso αᴰ ⋆PshIso ∫PshIso βᴰ

-- module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {P : Presheaf C ℓP}
--   {Q : Presheaf C ℓQ}
--   (α : PshIso P Q)
--   {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
--   {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
--   where
--   mkPshIsoᴰ :
--     (αᴰ : PshHomᴰ (α .trans) Pᴰ Qᴰ)
--     → (αᴰ⁻ : PshHomᴰ (invPshIso α .trans) Qᴰ Pᴰ)
--     → PathP (λ i → PshHomᴰ {!!} Qᴰ Qᴰ) (αᴰ⁻ ⋆PshHomᴰ αᴰ) {!!}
--     → {!!} ≡ {!!}
--     → PshIsoᴰ α Pᴰ Qᴰ
--   mkPshIsoᴰ αᴰ αᴰ⁻ s r .fst = αᴰ
--   mkPshIsoᴰ αᴰ αᴰ⁻ s r .snd .inv = λ _ → αᴰ⁻ .N-obᴰ
--   mkPshIsoᴰ αᴰ αᴰ⁻ s r .snd .rightInv = {!!}
--   mkPshIsoᴰ αᴰ αᴰ⁻ s r .snd .leftInv = {!!}

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  module _ {α : PshIso P Q} where
    invPshIsoᴰ : PshIsoᴰ α Pᴰ Qᴰ → PshIsoᴰ (invPshIso α) Qᴰ Pᴰ
    invPshIsoᴰ αᴰ = record
      { N-obᴰ = αᴰ .snd .inv _
      ; N-homᴰ = Pᴰ.rectify $ Pᴰ.≡out $ ∫αᴰ⁻ .trans .N-hom _ _ _ _
      }
      , isisoover (λ a → αᴰ .fst .N-obᴰ) (αᴰ .snd .leftInv) (αᴰ .snd .rightInv)
      where
        module Pᴰ = PresheafᴰNotation Pᴰ
        ∫αᴰ⁻ = invPshIso (∫PshIso αᴰ)

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
  infixr 9 _⋆PshHomⱽ_
  infixr 9 _⋆PshIsoⱽ_

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
          ∙ cong (∫αᴰ .trans .N-ob _) Pᴰ.⟨ refl ⟩⋆⟨ (sym $ Pᴰ.reind-filler _ _) ⟩
          ∙ ∫αᴰ .trans .N-hom _ _ _ _
          ∙ Qᴰ.⟨ refl ⟩⋆⟨ cong (∫αᴰ .trans .N-ob _) (cong (∫αᴰ .nIso _ .fst) (sym $ Qᴰ.reind-filler _ _))
                 ∙ ∫αᴰ .nIso _ .snd .fst _ ⟩
        )))
    where
      ∫αᴰ : PshIso (∫P Pᴰ) (∫P Qᴰ)
      ∫αᴰ = ∫PshIso αᴰ

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf D ℓP}
  {Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ}
  {Q : Presheaf D ℓQ}
  {Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
  where
  _∘ˡᴰ_ : ∀ {α : PshHom P Q} {F : Functor C D}
    (αᴰ : PshHomᴰ α Pᴰ Qᴰ) (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    → PshHomᴰ (α ∘ˡ F) (Pᴰ ∘Fᴰ (Fᴰ ^opFᴰ)) (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
  (αᴰ ∘ˡᴰ Fᴰ) .N-obᴰ = αᴰ .N-obᴰ
  (αᴰ ∘ˡᴰ Fᴰ) .N-homᴰ = αᴰ .N-homᴰ

  _∘ˡⁱᴰ_ : ∀ {α : PshIso P Q} {F : Functor C D}
    (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    → PshIsoᴰ (α ∘ˡⁱ F) (Pᴰ ∘Fᴰ (Fᴰ ^opFᴰ)) (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
  (αᴰ ∘ˡⁱᴰ Fᴰ) .fst = αᴰ .fst ∘ˡᴰ Fᴰ
  (αᴰ ∘ˡⁱᴰ Fᴰ) .snd .inv = αᴰ .snd .inv
  (αᴰ ∘ˡⁱᴰ Fᴰ) .snd .rightInv = αᴰ .snd .rightInv
  (αᴰ ∘ˡⁱᴰ Fᴰ) .snd .leftInv = αᴰ .snd .leftInv

  -- TODO: whiskering for universal element
