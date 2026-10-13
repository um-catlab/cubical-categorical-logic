{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.LocalRepresentability.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Properties
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Bifunctorᴰ
open Functorᴰ
open Section

open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  LocallyRepresentableᴰ :
    ((P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P)
    → Presheafᴰ P Cᴰ ℓPᴰ
    → Type _
  LocallyRepresentableᴰ (P , _×P) Pᴰ = ∀ {c} cᴰ → UniversalElementᴰ Cᴰ (c ×P) ((Cᴰ [-][-, cᴰ ]) ×ᴰPsh Pᴰ)

  open UniversalElement
  ∫LocallyRepresentable :
    {(P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P}
    → ((Pᴰ , _×ᴰPᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableᴰ (P , _×P) Pᴰ)
    → LocallyRepresentable (∫P Pᴰ)
  ∫LocallyRepresentable (Pᴰ , _×ᴰPᴰ) (Γ , Γᴰ) =
    UniversalElementᴰ.∫ue (Γᴰ ×ᴰPᴰ)
      ◁PshIso
      (∫×ᴰ≅× ⋆PshIso ×PshIso (TotalCatYoPshIso Cᴰ) idPshIso)

  -- This can't be written as simply UniversalElementsⱽ of some
  -- Profunctorⱽ because the definition of Presheafⱽ depends on Γ.
  LocallyRepresentableⱽ : {P : Presheaf C ℓP} → (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Type _
  LocallyRepresentableⱽ {P = P} Pᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
    → UniversalElementⱽ Cᴰ Γ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)
    where module P = PresheafNotation P

module _ {C : Category ℓC ℓC'} where
  LRᴰPresheafᴰ :
    ((P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P)
    → Categoryᴰ C ℓCᴰ ℓCᴰ'
    → (ℓPᴰ : Level)
    → Type _
  LRᴰPresheafᴰ P Cᴰ ℓPᴰ = Σ (Presheafᴰ (P .fst) Cᴰ ℓPᴰ) (LocallyRepresentableᴰ P)

  LRⱽPresheafᴰ :
    (P : Presheaf C ℓP)
    → Categoryᴰ C ℓCᴰ ℓCᴰ'
    → (ℓPᴰ : Level)
    → Type _
  LRⱽPresheafᴰ P Cᴰ ℓPᴰ = Σ (Presheafᴰ P Cᴰ ℓPᴰ) LocallyRepresentableⱽ
