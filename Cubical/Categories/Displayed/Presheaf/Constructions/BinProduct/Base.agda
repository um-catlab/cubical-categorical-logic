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

open import Cubical.Categories.LocallySmall
open import Cubical.Categories.LocallySmall.Functor as LocallySmall
open import Cubical.Categories.LocallySmall.Bifunctor as LocallySmall

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor as Small
open import Cubical.Categories.Displayed.Functor.More as Small
open import Cubical.Categories.Displayed.Bifunctor as Small
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base renaming (PRESHEAFᴰ to SmallPRESHEAFᴰ)
open import Cubical.Categories.Displayed.Presheaf.Properties
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf.Morphism

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Small.Bifunctorᴰ
open Small.Functorᴰ

open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  -- External product: (Pᴰ ×ᴰ Qᴰ) over (P × Q)
  PshProd'ᴰ :
    Small.Functorᴰ PshProd' (SmallPRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×Cᴰ SmallPRESHEAFᴰ Cᴰ ℓB ℓBᴰ)
                      (SmallPRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ))
  PshProd'ᴰ = postcomposeFᴰ (C ^op) (Cᴰ ^opᴰ) ×Setsᴰ ∘Fᴰ ,Fᴰ-functorᴰ

  PshProdᴰ :
    Small.Bifunctorᴰ PshProd (SmallPRESHEAFᴰ Cᴰ ℓA ℓAᴰ) (SmallPRESHEAFᴰ Cᴰ ℓB ℓBᴰ)
                       (SmallPRESHEAFᴰ Cᴰ (ℓ-max ℓA ℓB) (ℓ-max ℓAᴰ ℓBᴰ))
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
    Small.Functorⱽ (SmallPRESHEAFᴰ Cᴰ ℓA ℓAᴰ ×ᴰ SmallPRESHEAFᴰ Cᴰ ℓA ℓBᴰ)
             (SmallPRESHEAFᴰ Cᴰ ℓA (ℓ-max ℓAᴰ ℓBᴰ))
  PshProdⱽ = postcomposeFⱽ (C ^op) (Cᴰ ^opᴰ) ×Setsⱽ ∘Fⱽ ,Fⱽ-functorⱽ

  _×ⱽPsh_ : ∀ {P : Presheaf C ℓA}
            → (Pᴰ : Presheafᴰ P Cᴰ ℓAᴰ)(Qᴰ : Presheafᴰ P Cᴰ ℓBᴰ)
            → Presheafᴰ P Cᴰ _
  Pᴰ ×ⱽPsh Qᴰ = PshProdⱽ .F-obᴰ (Pᴰ , Qᴰ)

  open Bifunctorⱽ
  PshProdⱽ' : Bifunctorⱽ idF (PRESHEAFᴰ Cᴰ) (PRESHEAFᴰ Cᴰ) (PRESHEAFᴰ Cᴰ)
  PshProdⱽ' .Bif-obᴰ (_ , liftω Pᴰ) (_ , liftω Qᴰ) = _ , liftω (Pᴰ ×ⱽPsh Qᴰ)
  PshProdⱽ' .Bif-hom×ᴰ {c' = (_ , liftω Q)} αᴰ βᴰ = pshhomᴰ (λ {x} {xᴰ} {p} z →
                                           αᴰ .PshHomᴰ.N-obᴰ (z .fst) , βᴰ .PshHomᴰ.N-obᴰ (z .snd))
                                             (×≡Snd-hSet (PresheafNotation.isSetPsh Q)
                                               (αᴰ .PshHomᴰ.N-homᴰ) (βᴰ .PshHomᴰ.N-homᴰ))
  PshProdⱽ' .Bif-×-idᴰ = makePshHomᴰPath refl (λ _ → refl)
  PshProdⱽ' .Bif-×-seqᴰ = makePshHomᴰPath refl (λ _ → refl)

  -- LocallyRepresentableᴰ :
  --   ((P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P)
  --   → Presheafᴰ P Cᴰ ℓPᴰ
  --   → Type _
  -- LocallyRepresentableᴰ (P , _×P) Pᴰ = ∀ {c} cᴰ → UniversalElementᴰ Cᴰ (c ×P) ((Cᴰ [-][-, cᴰ ]) ×ᴰPsh Pᴰ)

  -- open UniversalElement
  -- ∫LocallyRepresentable :
  --   {(P , _×P) : Σ[ P ∈ Presheaf C ℓP ] LocallyRepresentable P}
  --   → ((Pᴰ , _×ᴰPᴰ) : Σ[ Pᴰ ∈ Presheafᴰ P Cᴰ ℓPᴰ ] LocallyRepresentableᴰ (P , _×P) Pᴰ)
  --   → LocallyRepresentable (∫P Pᴰ)
  -- ∫LocallyRepresentable (Pᴰ , _×ᴰPᴰ) (Γ , Γᴰ) =
  --   UniversalElementᴰ.∫ue (Γᴰ ×ᴰPᴰ)
  --     ◁PshIso
  --     (∫×ᴰ≅× ⋆PshIso ×PshIso (TotalCatYoPshIso Cᴰ) idPshIso)

  -- LocallyRepresentableⱽ : {P : Presheaf C ℓP} → (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) → Type _
  -- LocallyRepresentableⱽ {P = P} Pᴰ = ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
  --   → UniversalElementⱽ Cᴰ Γ ((Cᴰ [-][-, Γᴰ ]) ×ⱽPsh reindYo p Pᴰ)
  --   where module P = PresheafNotation P
