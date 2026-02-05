{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Cartesian where
-- TODO still need better name

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.HITs.PathEq
open import Cubical.HITs.Join

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.BinProduct as BP hiding (π₁ ; π₂)
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
-- open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base hiding (PshHomᴰ ; _⋆PshHomᴰ_ ; PRESHEAFᴰ)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Base
open import Cubical.Categories.Presheaf.StrictHom


open Functor
open Iso
open NatIso
open NatTrans
open Categoryᴰ
open PshHomStrict
open PshHom
open PshIso

private
  variable
    ℓ ℓ' ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{ℓP}{ℓPᴰ} where
  PSHᴰTerminalsⱽ : Terminalsⱽ (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ)
  PSHᴰTerminalsⱽ P = UEⱽ→Reprⱽ UnitⱽPsh PSHIdR termⱽ
    where
      termⱽ : UEⱽ UnitⱽPsh PSHIdR
      termⱽ .UEⱽ.v = Unit*Psh
      termⱽ .UEⱽ.e = tt
      termⱽ .UEⱽ.universal .isPshIsoEq.nIso (R , Rᴰ , α) .fst tt =
        Unit*Psh-intro ⋆PshHom invPshIso (reindPsh-Unit* _) .trans
      termⱽ .UEⱽ.universal .isPshIsoEq.nIso (R , Rᴰ , α) .snd .fst _ = refl
      termⱽ .UEⱽ.universal .isPshIsoEq.nIso (R , Rᴰ , α) .snd .snd αᴰ = makePshHomPath refl

  PSHᴰBPⱽ : BinProductsⱽ (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ)
  PSHᴰBPⱽ {x = P} Pᴰ Qᴰ = UEⱽ→Reprⱽ _ PSHIdR bpⱽ where
    bpⱽ : UEⱽ ((PRESHEAFᴰ Cᴰ ℓP ℓPᴰ [-][-, Pᴰ ]) ×ⱽPsh (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ [-][-, Qᴰ ])) PSHIdR
    bpⱽ .UEⱽ.v = Pᴰ ×Psh Qᴰ
    bpⱽ .UEⱽ.e = (BP.π₁ Pᴰ Qᴰ ⋆PshHom idPshHomᴰ) , BP.π₂ Pᴰ Qᴰ ⋆PshHom idPshHomᴰ
    bpⱽ .UEⱽ.universal .isPshIsoEq.nIso (R , Rᴰ , α) .fst (αᴰP , αᴰQ) = ×PshIntro αᴰP αᴰQ ⋆PshHom invPshIso (reindPsh× _ Pᴰ Qᴰ) .trans
    bpⱽ .UEⱽ.universal .isPshIsoEq.nIso (R , Rᴰ , α) .snd .fst αᴰ@(αᴰP , αᴰQ) = ≡-× (makePshHomPath refl) (makePshHomPath refl)
    bpⱽ .UEⱽ.universal .isPshIsoEq.nIso (R , Rᴰ , α) .snd .snd αᴰ× = makePshHomPath refl

  PSHᴰFibration : Fibration (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ) PSHAssoc
  PSHᴰFibration {x = P}{y = Q} α Qᴰ = UEⱽ→Reprⱽ _ PSHIdR fib where
    fib : UEⱽ (yoRecEq (PRESHEAF C ℓP [-, Q ]) (PSHAssoc Q) α *Presheafᴰ (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ [-][-, Qᴰ ])) PSHIdR
    fib .UEⱽ.v = α *Strict Qᴰ
    fib .UEⱽ.e = idPshHom
    fib .UEⱽ.universal .isPshIsoEq.nIso (R , Rᴰ , β) .fst βᴰ = βᴰ ⋆PshHom *Strict-seq⁻ β α
    fib .UEⱽ.universal .isPshIsoEq.nIso (R , Rᴰ , β) .snd .fst βᴰ = makePshHomPath refl
    fib .UEⱽ.universal .isPshIsoEq.nIso (R , Rᴰ , β) .snd .snd βᴰ = makePshHomPath refl

  isCartesianⱽPSHᴰ : isCartesianⱽ PSHAssoc (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ)
  isCartesianⱽPSHᴰ .fst = PSHᴰTerminalsⱽ
  isCartesianⱽPSHᴰ .snd .fst = PSHᴰBPⱽ
  isCartesianⱽPSHᴰ .snd .snd = PSHᴰFibration
