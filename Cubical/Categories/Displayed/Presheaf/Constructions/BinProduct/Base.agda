{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

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
open import Cubical.Categories.Displayed.Presheaf.Properties
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Base
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

open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  -- External product: (Pᴰ ×ᴰ Qᴰ) over (P × Q)
  PshProd'ᴰ :
    Functorᴰ PshProd' (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×Cᴰ PRESHEAFᴰ Cᴰ ℓB ℓBᴰ)
                      (PRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ))
  PshProd'ᴰ = postcomposeFᴰ (C ^op) (Cᴰ ^opᴰ) ×Setsᴰ ∘Fᴰ ,Fᴰ-functorᴰ

  PshProdᴰ :
    Bifunctorᴰ PshProd (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ) (PRESHEAFᴰ Cᴰ ℓB ℓBᴰ)
                       (PRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ))
  PshProdᴰ = ParFunctorᴰToBifunctorᴰ PshProd'ᴰ

  _×ᴰPsh_ : ∀ {P : Presheaf C ℓA}{Q : Presheaf C ℓB}
            → (Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓBᴰ)
            → Presheafᴰ (P ×Psh Q) Cᴰ _
  _×ᴰPsh_ = PshProdᴰ .Bif-obᴰ

  ∫×ᴰ≅× : ∀ {P : Presheaf C ℓA}{Q : Presheaf C ℓB}
            → {Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓBᴰ}
        → PshIso (∫P (Pᴰ ×ᴰPsh Qᴰ)) (∫P Pᴰ ×Psh ∫P Qᴰ)
  ∫×ᴰ≅× .trans .N-ob _ ((p , q) , (pᴰ , qᴰ)) = (p , pᴰ) , (q , qᴰ)
  ∫×ᴰ≅× .trans .N-hom _ _ _ _ = refl
  ∫×ᴰ≅× .nIso _ .fst ((p , pᴰ) , (q , qᴰ)) = (p , q) , (pᴰ , qᴰ)
  ∫×ᴰ≅× .nIso _ .snd .fst _ = refl
  ∫×ᴰ≅× .nIso _ .snd .snd _ = refl

  -- Internal product: Pᴰ ×ⱽ Qᴰ over P
  PshProdⱽ :
    Functorⱽ (PRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×ᴰ PRESHEAFᴰ Cᴰ ℓA ℓBᴰ)
             (PRESHEAFᴰ Cᴰ ℓA (ℓ-max ℓAᴰ ℓBᴰ))
  PshProdⱽ = postcomposeFⱽ (C ^op) (Cᴰ ^opᴰ) ×Setsⱽ ∘Fⱽ ,Fⱽ-functorⱽ

  _×ⱽPsh_ : ∀ {P : Presheaf C ℓA}
            → (Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ)(Qᴰ : Presheafᴰ P Cᴰ ℓBᴰ)
            → Presheafᴰ P Cᴰ _
  Pᴰ ×ⱽPsh Qᴰ = PshProdⱽ .F-obᴰ (Pᴰ , Qᴰ)

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

  LocallyRepresentableⱽ : {P : Presheaf C ℓP} → (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Type _
  LocallyRepresentableⱽ {P = P} Pᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
    → UniversalElementⱽ Cᴰ Γ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)
    where module P = PresheafNotation P
