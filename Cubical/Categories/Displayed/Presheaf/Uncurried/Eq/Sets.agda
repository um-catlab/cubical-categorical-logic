{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
open import Cubical.Categories.Displayed.Instances.Sets.Base as Setᴰ hiding (_[-][-,_])
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq
import Cubical.Categories.Displayed.Presheaf.Base as Curried
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Category
open Functor
open Functorᴰ
open isIsoOver
open NatTrans
open NatTransᴰ
open NatIso
open NatIsoᴰ
open PshHom
open PshIso

SetIdR : EqIdR (SET ℓ)
SetIdR = λ f → Eq.refl

SetIdL : EqIdL (SET ℓ)
SetIdL = λ f → Eq.refl

SetAssoc : ReprEqAssoc (SET ℓ)
SetAssoc x f g p f⋆g Eq.refl = Eq.refl

Setπ₁NatEq : Allπ₁NatEq {C = SET ℓ} BinProductsSET
Setπ₁NatEq X γ = Eq.refl

Set×aF-seq : All×aF-seq {C = SET ℓ} BinProductsSET
Set×aF-seq X δ γ = Eq.refl

SetᴰTerminalsⱽ : Terminalsⱽ (SETᴰ ℓ ℓᴰ)
SetᴰTerminalsⱽ X .fst x .fst = Unit*
SetᴰTerminalsⱽ X .fst x .snd = isSetUnit*
SetᴰTerminalsⱽ X .snd .PshIsoEq.isos c .Iso.fun = λ _ → tt
SetᴰTerminalsⱽ X .snd .PshIsoEq.isos c .Iso.inv = λ _ x _ → tt*
SetᴰTerminalsⱽ X .snd .PshIsoEq.isos c .Iso.sec b = refl
SetᴰTerminalsⱽ X .snd .PshIsoEq.isos c .Iso.ret a = refl
SetᴰTerminalsⱽ X .snd .PshIsoEq.nat c c' f p' p x = Eq.refl

SetᴰBPⱽ : BinProductsⱽ (SETᴰ ℓ ℓᴰ)
SetᴰBPⱽ {x = X} P Q = UEⱽ→Reprⱽ _ SetIdR ueⱽ
  where
    ueⱽ : UEⱽ ((SETᴰ _ _ [-][-, P ]) ×ⱽPsh (SETᴰ _ _ [-][-, Q ])) SetIdR
    ueⱽ .UEⱽ.v x .fst = ⟨ P x ⟩ × ⟨ Q x ⟩
    ueⱽ .UEⱽ.v x .snd = isSet× (P x .snd) (Q x .snd)
    ueⱽ .UEⱽ.e = (λ x (p , q) → p) , (λ x (p , q) → q)
    ueⱽ .UEⱽ.universal .isPshIsoEq.nIso (Z , R , x⟨z⟩) .fst (p , q) r z = p r z , q r z
    ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst b = refl
    ueⱽ .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd a = refl

SetᴰFibration : Fibration (SETᴰ ℓ ℓᴰ) SetAssoc
SetᴰFibration {ℓ} {ℓᴰ} {X} {Y} f Q = UEⱽ→Reprⱽ _ SetIdR fibUE
  where
    fibUE : UEⱽ (yoRecEq (SET ℓ [-, Y ]) (SetAssoc Y) f *Presheafᴰ (SETᴰ ℓ ℓᴰ [-][-, Q ])) SetIdR
    fibUE .UEⱽ.v x = Q (f x)
    fibUE .UEⱽ.e x q = q
    fibUE .UEⱽ.universal .isPshIsoEq.nIso (Z , R , x⟨z⟩) = IsoToIsIso idIso

isCartesianⱽSETᴰ : isCartesianⱽ SetAssoc (SETᴰ ℓ ℓᴰ)
isCartesianⱽSETᴰ = SetᴰTerminalsⱽ , (SetᴰBPⱽ , SetᴰFibration)

SetᴰLRⱽ : AllLRⱽ (SETᴰ ℓ ℓᴰ) SetAssoc
SetᴰLRⱽ {ℓ} {ℓᴰ} = BPⱽ+Fibration→AllLRⱽ (SETᴰ ℓ ℓᴰ) SetAssoc SetᴰBPⱽ SetᴰFibration

SETᴰExpsⱽ : Exponentialsⱽ (SETᴰ ℓ ℓᴰ) SetAssoc SetIdL SetᴰLRⱽ
SETᴰExpsⱽ {ℓ} {ℓᴰ} {X} P Q  = UEⱽ→Reprⱽ _ SetIdR expUE
    where
      expUE : UEⱽ (reindPsh (LRⱽF (SETᴰ ℓ ℓᴰ) SetAssoc SetIdL P (SetᴰLRⱽ P)) (SETᴰ ℓ ℓᴰ [-][-, Q ]))
                  SetIdR
      expUE .UEⱽ.v x .fst = ⟨ P x ⟩ → ⟨ Q x ⟩
      expUE .UEⱽ.v x .snd = isSet→ (Q x .snd)
      expUE .UEⱽ.e x (f , p) = f p
      expUE .UEⱽ.universal .isPshIsoEq.nIso (Z , R , x⟨z⟩) .fst f⟨z,r,p⟩ z r p = f⟨z,r,p⟩ z (r , p)
      expUE .UEⱽ.universal .isPshIsoEq.nIso (Z , R , x⟨z⟩) .snd .fst b = refl
      expUE .UEⱽ.universal .isPshIsoEq.nIso (Z , R , x⟨z⟩) .snd .snd a = refl

SETᴰ∀ : UniversalQuantifiers (SETᴰ ℓ ℓ) SetIdL SetAssoc (isCartesianⱽSETᴰ .snd .snd) BinProductsSET Setπ₁NatEq Set×aF-seq
SETᴰ∀ {ℓ} X {Y} P = UEⱽ→Reprⱽ _ SetIdR ueⱽ
  where
    ueⱽ : UEⱽ (reindPsh
               (wkF (SETᴰ ℓ ℓ) SetIdL SetAssoc (isCartesianⱽSETᴰ .snd .snd) X
                (λ c → BinProductsSET (c , X)) (Setπ₁NatEq X) (Set×aF-seq X) Y)
               (SETᴰ ℓ ℓ [-][-, P ])) SetIdR
    ueⱽ .UEⱽ.v y .fst = ∀ x → ⟨ P (y , x) ⟩
    ueⱽ .UEⱽ.v y .snd = isSetΠ λ x → P (y , x) .snd
    ueⱽ .UEⱽ.e (y , x) ∀x∙p = ∀x∙p x
    ueⱽ .UEⱽ.universal .isPshIsoEq.nIso (Z , R , y⟨z⟩) .fst py⟨z,x,r⟩ z r x = py⟨z,x,r⟩ (z , x) r
    ueⱽ .UEⱽ.universal .isPshIsoEq.nIso (Z , R , y⟨z⟩) .snd .fst b = refl
    ueⱽ .UEⱽ.universal .isPshIsoEq.nIso (Z , R , y⟨z⟩) .snd .snd a = refl

isCCCⱽSETᴰ : isCartesianClosedⱽ SetAssoc (SETᴰ ℓ ℓ) SetIdL BinProductsSET Setπ₁NatEq Set×aF-seq
isCCCⱽSETᴰ .fst = isCartesianⱽSETᴰ
isCCCⱽSETᴰ .snd .fst = SETᴰExpsⱽ
isCCCⱽSETᴰ .snd .snd = SETᴰ∀
