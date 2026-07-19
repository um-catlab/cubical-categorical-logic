{-# OPTIONS --lossy-unification #-}
-- STAGE 1 OF THE DIRECT REBUILD: the `GuardedLogic (SET)` semantic model
-- over `Fam (PRESHEAF ℕCat)` — the topos of trees with OUR later/löb,
-- replacing `ωSETᴰ-Guarded` of `Gluing/Category/GuardedFixedPoint.agda`.
-- The generic `Fam`/`FamTerminalsⱽ`/`isFibrationFam`/`FamF`/`Fam-PtNT`
-- machinery is instantiated at `PRESHEAF ℕCat`; `gfpⱽ` is wired to our
-- `guarded-fixed-points-Psh` (= `löb`).
module Cubical.Categories.Instances.PshℕGuardedModel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.FixedPoint
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed using (UnitPsh-introStrict)

open import Cubical.Categories.Instances.Fiber hiding (fiber)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.FixedPoint
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Instances.Family.Base
open import Cubical.Categories.Displayed.Instances.Family.Properties
open import Cubical.Categories.Displayed.Instances.Family.EqProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Sets

open import Cubical.Categories.Direct.Instances.Nat using (ℕCat ; ℕDirect)
open import Cubical.Categories.Direct.StrictDownset using (▷ ; nextNT)
open import Cubical.Categories.Instances.PshℕGuarded
  using (▷ℕ ; nextℕ ; guarded-fixed-points-Psh)

open Category
open Categoryᴰ
open Functor
open UniversalElement

-- the terminal presheaf on ℕCat with vertex `UnitPsh` (so it matches the
-- `UnitPsh` domain of `löb`)
UnitPsh-Terminal : Terminal' (PRESHEAF ℕCat ℓ-zero)
UnitPsh-Terminal .vertex  = UnitPsh
UnitPsh-Terminal .element = tt
UnitPsh-Terminal .universal _ =
  isoToIsEquiv (iso (λ _ → tt) (λ _ → UnitPsh-introStrict) (λ _ → refl) (λ _ → refl))

-- the displayed category (fibration) of ℕ-presheaf families over SET
Pshℕᴰ0 : Categoryᴰ (SET ℓ-zero) (ℓ-suc ℓ-zero) ℓ-zero
Pshℕᴰ0 = Fam (PRESHEAF ℕCat ℓ-zero)

module Pshℕᴰ0 = Fibers Pshℕᴰ0

Pshℕᴰ-Terminalsⱽ : Terminalsⱽ Pshℕᴰ0
Pshℕᴰ-Terminalsⱽ = EqTerminalsⱽ→Terminalsⱽ SetAssoc Pshℕᴰ0
  (FamTerminalsⱽ {ℓ = ℓ-zero} (PRESHEAF ℕCat ℓ-zero) UnitPsh-Terminal)

Pshℕᴰ-fibration : isFibration Pshℕᴰ0
Pshℕᴰ-fibration = EqFibration→Fibration {C = SET ℓ-zero}
  SetAssoc
  Pshℕᴰ0
  (isFibrationFam {ℓ = ℓ-zero} (PRESHEAF ℕCat ℓ-zero))

Pshℕᴰ-Guarded : GuardedLogic (SET ℓ-zero) _ _
Pshℕᴰ-Guarded .GuardedLogic.Cᴰ = Pshℕᴰ0
Pshℕᴰ-Guarded .GuardedLogic.▷ⱽ = FamF (▷ ℕDirect)
Pshℕᴰ-Guarded .GuardedLogic.next = Fam-PtNT (nextNT ℕDirect)
Pshℕᴰ-Guarded .GuardedLogic.isFibCᴰ = Pshℕᴰ-fibration
Pshℕᴰ-Guarded .GuardedLogic.termⱽ = Pshℕᴰ-Terminalsⱽ
Pshℕᴰ-Guarded .GuardedLogic.gfpⱽ {A = X} {Aᴰ = Xᴰ} fⱽ =
  fixed-pointⱽ'→ⱽ _ _ _ _
    (subst (fixed-pointⱽ' Pshℕᴰ0 X (Pshℕᴰ-Terminalsⱽ X .fst))
      (Pshℕᴰ0.rectifyOut {a = X} {b = X} {aᴰ = Xᴰ} {bᴰ = Xᴰ} {e' = refl}
        (Pshℕᴰ0.reind-filler _))
      ( (λ x → guarded-fixed-points-Psh (fⱽ x) .fst)
      , funExt (λ x → guarded-fixed-points-Psh (fⱽ x) .snd) ))
