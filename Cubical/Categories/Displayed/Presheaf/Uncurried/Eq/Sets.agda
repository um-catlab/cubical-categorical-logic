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

SetᴰTerminalsⱽ : Terminalsⱽ (SETᴰ ℓ ℓᴰ)
SetᴰTerminalsⱽ X .fst x .fst = Unit*
SetᴰTerminalsⱽ X .fst x .snd = isSetUnit*
SetᴰTerminalsⱽ X .snd .PshIsoEq.isos c .Iso.fun = λ _ → tt
SetᴰTerminalsⱽ X .snd .PshIsoEq.isos c .Iso.inv = λ _ x _ → tt*
SetᴰTerminalsⱽ X .snd .PshIsoEq.isos c .Iso.sec b = refl
SetᴰTerminalsⱽ X .snd .PshIsoEq.isos c .Iso.ret a = refl
SetᴰTerminalsⱽ X .snd .PshIsoEq.nat c c' f p' p x = Eq.refl

SetᴰBPⱽ : BinProductsⱽ (SETᴰ ℓ ℓᴰ)
SetᴰBPⱽ {x = X} P Q .fst x .fst = ⟨ P x ⟩ × ⟨ Q x ⟩
SetᴰBPⱽ {x = X} P Q .fst x .snd = isSet× (P x .snd) (Q x .snd)
SetᴰBPⱽ {x = X} P Q .snd .PshIsoEq.isos c .Iso.fun = λ z → (λ x z₁ → z x z₁ .fst) , (λ x z₁ → z x z₁ .snd)
SetᴰBPⱽ {x = X} P Q .snd .PshIsoEq.isos c .Iso.inv = λ z x z₁ → z .fst x z₁ , z .snd x z₁
SetᴰBPⱽ {x = X} P Q .snd .PshIsoEq.isos c .Iso.sec b = refl
SetᴰBPⱽ {x = X} P Q .snd .PshIsoEq.isos c .Iso.ret a = refl
SetᴰBPⱽ {x = X} P Q .snd .PshIsoEq.nat c c' (_ , _ , Eq.refl) p' p Eq.refl = Eq.refl

SetᴰBPⱽUE : BinProductsⱽUE (SETᴰ ℓ ℓᴰ) λ {x} {y} f → Eq.refl
SetᴰBPⱽUE {ℓ} {ℓᴰ} {X} P Q .UEⱽ.v x .fst = ⟨ P x ⟩ × ⟨ Q x ⟩
SetᴰBPⱽUE {ℓ} {ℓᴰ} {X} P Q .UEⱽ.v x .snd = isSet× (P x .snd) (Q x .snd)
SetᴰBPⱽUE {ℓ} {ℓᴰ} {X} P Q .UEⱽ.e = (λ x z → z .fst) , (λ x z → z .snd)
SetᴰBPⱽUE {ℓ} {ℓᴰ} {X} P Q .UEⱽ.universal .isPshIsoEq.nIso c .fst = λ z x z₁ → z .fst x z₁ , z .snd x z₁
SetᴰBPⱽUE {ℓ} {ℓᴰ} {X} P Q .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst b = refl
SetᴰBPⱽUE {ℓ} {ℓᴰ} {X} P Q .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd a = refl

SetᴰFibration : Fibration (SETᴰ ℓ ℓᴰ) SetAssoc
SetᴰFibration {ℓ} {ℓᴰ} {X} {Y} f Q = UEⱽ→Reprⱽ _ SetIdR fibUE
  where
    fibUE : UEⱽ
      (yoRecEq (SET ℓ [-, Y ]) (SetAssoc Y) f *Presheafᴰ
         (SETᴰ ℓ ℓᴰ [-][-, Q ]))
        SetIdR
    fibUE .UEⱽ.v = λ z → Q (f z)
    fibUE .UEⱽ.e = λ x z → z
    fibUE .UEⱽ.universal .isPshIsoEq.nIso c = IsoToIsIso idIso

module _ {X : SET ℓ .ob}(P : SETᴰ ℓ ℓᴰ .Categoryᴰ.ob[_] X) where
  SetᴰLRⱽ : LRⱽ (SETᴰ ℓ ℓᴰ) SetAssoc P
  SetᴰLRⱽ {Γ} Γᴰ f = UEⱽ→Reprⱽ _ SetIdR lrⱽue
    where
      lrⱽue : UEⱽ
        ((SETᴰ ℓ ℓᴰ [-][-, Γᴰ ]) ×ⱽPsh
         (yoRecEq (SET ℓ [-, X ]) (SetAssoc X) f *Presheafᴰ
          (SETᴰ ℓ ℓᴰ [-][-, P ])))
        SetIdR
      lrⱽue .UEⱽ.v γ .fst = ⟨ Γᴰ γ ⟩ × ⟨ P (f γ ) ⟩
      lrⱽue .UEⱽ.v γ .snd = isSet× (Γᴰ γ .snd) (P (f γ) .snd)
      lrⱽue .UEⱽ.e = (λ x z → z .fst) , (λ x z → z .snd)
      lrⱽue .UEⱽ.universal .isPshIsoEq.nIso c .fst = λ z x z₁ → z .fst x z₁ , z .snd x z₁
      lrⱽue .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst b = refl
      lrⱽue .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd a = refl

  SETᴰExpsⱽ : Exponentialsⱽ (SETᴰ ℓ ℓᴰ) SetAssoc SetIdL P SetᴰLRⱽ
  SETᴰExpsⱽ Q = UEⱽ→Reprⱽ _ SetIdR expUE
    where
      expUE : UEⱽ
        (reindPsh (LRⱽF (SETᴰ ℓ ℓᴰ) SetAssoc SetIdL P SetᴰLRⱽ)
         (SETᴰ ℓ ℓᴰ [-][-, Q ]))
        SetIdR
      expUE .UEⱽ.v x .fst = ⟨ P x ⟩ → ⟨ Q x ⟩
      expUE .UEⱽ.v x .snd = isSet→ (Q x .snd)
      expUE .UEⱽ.e = λ x z → z .fst (z .snd)
      expUE .UEⱽ.universal .isPshIsoEq.nIso c .fst = λ z x z₁ z₂ → z x (z₁ , z₂)
      expUE .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst b = refl
      expUE .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd a = refl

module _ {X : SET ℓ .ob} where
  SETUniversalQuantifiers : UniversalQuantifiers (SETᴰ ℓ ℓ) SetIdL SetAssoc
    {x = X}
    (λ c → BinProductsSET (c , X))
    SetᴰFibration
    (λ {Δ} {Γ} γ → Eq.refl)
    λ {Θ} {Δ} {Γ} δ γ → Eq.refl
  SETUniversalQuantifiers {Γ = Y} Q = UEⱽ→Reprⱽ _ SetIdR ∀ue
    where
      ∀ue : UEⱽ
        (reindPsh
         (wkF (SETᴰ ℓ ℓ) SetIdL SetAssoc (λ c → BinProductsSET (c , X))
          SetᴰFibration (λ {Δ} {Γ} γ → Eq.refl) (λ {Θ} {Δ} {Γ} δ γ → Eq.refl)
          Y)
         (SETᴰ ℓ ℓ [-][-, Q ]))
        SetIdR
      ∀ue .UEⱽ.v y .fst = ∀ x → ⟨ Q (y , x ) ⟩
      ∀ue .UEⱽ.v y .snd = isSetΠ (λ x → Q (y , x) .snd)
      ∀ue .UEⱽ.e = λ x z → z (snd x)
      ∀ue .UEⱽ.universal .isPshIsoEq.nIso c .fst = λ z x z₁ x₁ → z (x , x₁) z₁
      ∀ue .UEⱽ.universal .isPshIsoEq.nIso c .snd .fst b = refl
      ∀ue .UEⱽ.universal .isPshIsoEq.nIso c .snd .snd a = refl
