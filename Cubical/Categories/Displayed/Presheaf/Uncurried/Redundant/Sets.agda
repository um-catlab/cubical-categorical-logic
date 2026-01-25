{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.Sets where

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
open import Cubical.HITs.PathEq as PathEq
open import Cubical.HITs.Join as Join
open import Cubical.HITs.Join.More as Join

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
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
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.Base

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

SetᴰTerminalsⱽ : Terminalsⱽ (SETᴰ ℓ ℓᴰ)
SetᴰTerminalsⱽ X .fst x .fst = Unit*
SetᴰTerminalsⱽ X .fst x .snd = isSetUnit*
SetᴰTerminalsⱽ X .snd .PshIso'.isos c .Iso.fun = λ _ → tt
SetᴰTerminalsⱽ X .snd .PshIso'.isos c .Iso.inv = λ _ x _ → tt*
SetᴰTerminalsⱽ X .snd .PshIso'.isos c .Iso.sec = λ _ → refl
SetᴰTerminalsⱽ X .snd .PshIso'.isos c .Iso.ret = λ _ → refl
SetᴰTerminalsⱽ X .snd .PshIso'.nat c c' f p = inr Eq.refl

SetᴰBPⱽ : BinProductsⱽ (SETᴰ ℓ ℓᴰ)
SetᴰBPⱽ {x = X} P Q .fst x .fst = ⟨ P x ⟩ × ⟨ Q x ⟩
SetᴰBPⱽ {x = X} P Q .fst x .snd = isSet× (P x .snd) (Q x .snd)
SetᴰBPⱽ {x = X} P Q .snd .PshIso'.isos c .Iso.fun f .fst x xᴰ = f x xᴰ .fst
SetᴰBPⱽ {x = X} P Q .snd .PshIso'.isos c .Iso.fun f .snd x xᴰ = f x xᴰ .snd
SetᴰBPⱽ {x = X} P Q .snd .PshIso'.isos c .Iso.inv f x xᴰ .fst = f .fst x xᴰ
SetᴰBPⱽ {x = X} P Q .snd .PshIso'.isos c .Iso.inv f x xᴰ .snd = f .snd x xᴰ
SetᴰBPⱽ {x = X} P Q .snd .PshIso'.isos c .Iso.sec f = refl
SetᴰBPⱽ {x = X} P Q .snd .PshIso'.isos c .Iso.ret f = refl
SetᴰBPⱽ {x = X} P Q .snd .PshIso'.nat c c' = Hom/-elim (λ f fᴰ → elimPropEq (isSet→ (X .snd)) (λ _ → isPropΠ (λ _ → isPropPathEq (isSet× (isSetΠ λ _ → isSet→ (P _ .snd)) ((isSetΠ λ _ → isSet→ (Q _ .snd)))))) (λ { Eq.refl →
  λ g → inr Eq.refl }))

SetᴰFibration : Fibration (SETᴰ ℓ ℓᴰ) λ f g h → Eq.refl
SetᴰFibration {ℓ} {ℓᴰ} {X} {Y} f Q .fst x = Q (f x)
SetᴰFibration {ℓ} {ℓᴰ} {X} {Y} f Q .snd .PshIso'.isos (Γ , Γᴰ , g) = idIso
SetᴰFibration {ℓ} {ℓᴰ} {X} {Y} f Q .snd .PshIso'.nat (Δ , Δᴰ , γ) (Γ , Γᴰ , g) = Hom/-elim λ γ γᴰ → elimPropEq
  (isSet→ (X .snd))
  (λ _ → isPropΠ (λ _ → isPropPathEq (isSetΠ (λ _ → isSet→ (Q _ .snd)))))
  λ { Eq.refl → λ q → inr Eq.refl }
