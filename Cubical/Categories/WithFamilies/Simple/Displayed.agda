{-# OPTIONS --lossy-unification #-}
{-

  A displayed SCwF is an abstract notion of "logical family" over a SCwF

-}
module Cubical.Categories.WithFamilies.Simple.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Constructions.Fiber
-- open import Cubical.Categories.Constructions.TotalCategory.Limits
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More renaming (preservesTerminal to funcPreservesTerminal)
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.WithFamilies.Simple.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Sets.Base hiding (_[-][-,_])
open import Cubical.Categories.Displayed.Instances.Terminal as Terminal
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
-- open import Cubical.Categories.Displayed.Presheaf.Representable
-- open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
-- open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Section

private
  variable
    ℓC ℓC' ℓT ℓT' ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level

open UniversalElement
-- open UniversalElementᴰ
open Bifunctorᴰ
open isIsoOver
open Iso

record SCwFᴰ (S : SCwF ℓC ℓC' ℓT ℓT') (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level)
  : Type (ℓ-max
          (ℓ-max
           (ℓ-max
            (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓC) (ℓ-suc ℓC')) ℓT) ℓT')
             (ℓ-suc ℓCᴰ))
            (ℓ-suc ℓCᴰ'))
           (ℓ-suc ℓTᴰ))
          (ℓ-suc ℓTᴰ'))
  where
  open SCwF S
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    Tyᴰ : Ty → Type ℓTᴰ
    Tmᴰ : ∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ (Tm A) Cᴰ ℓTᴰ'
    termᴰ : Terminalᴰ Cᴰ term
    extᴰ : ∀ {A} (Aᴰ : Tyᴰ A) → isLRᴰ ((Tm A) , (ext A)) (Tmᴰ Aᴰ)
  module Cᴰ = Fibers Cᴰ
  module Tmᴰ {A} {Aᴰ : Tyᴰ A} = PresheafᴰNotation Cᴰ (Tm A) (Tmᴰ Aᴰ)
  Tmᴰ[_][_,_] : ∀ {Γ A}(M : Tm[ Γ , A ])(Γᴰ : Cᴰ.ob[ Γ ]) (Aᴰ : Tyᴰ A) → Type ℓTᴰ'
  Tmᴰ[ M ][ Γᴰ , Aᴰ ] = Tmᴰ.p[_][_] {Aᴰ = Aᴰ} M Γᴰ
  module termᴰ = UniversalElementᴰNotation {C = C} Cᴰ (UnitPsh {C = C}) (UnitPshᴰ {P = UnitPsh {C = C}}) {ue = term} termᴰ
  module _ {A} (Aᴰ : Tyᴰ A) where
    extᴰObᴰ = isLRᴰNotation.vertexᴰ (Tm A , ext A) (extᴰ Aᴰ)
  module _ {A} {Aᴰ : Tyᴰ A} where
    module extᴰ = isLRᴰNotation (Tm A , ext A) (extᴰ Aᴰ) hiding (vertexᴰ)

-- record SCwFⱽ (S : SCwF ℓC ℓC' ℓT ℓT') (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level)
--   : Type (ℓ-max
--           (ℓ-max
--            (ℓ-max
--             (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓC) (ℓ-suc ℓC')) ℓT) ℓT')
--              (ℓ-suc ℓCᴰ))
--             (ℓ-suc ℓCᴰ'))
--            (ℓ-suc ℓTᴰ))
--           (ℓ-suc ℓTᴰ'))
--   where
--   open SCwF S
--   field
--     Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
--     cartLifts : isFibration Cᴰ
--     allLRⱽ : AllLRⱽ Cᴰ
--     termⱽ : Terminalsⱽ Cᴰ
--     bpⱽ : BinProductsⱽ Cᴰ
--   --   expⱽ : Exponentialsⱽ Cᴰ allLRⱽ
--   module Cᴰ = Fibers Cᴰ

-- module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
--   private
--     module S = SCwF S
--   SCwFⱽ→ᴰ : (Sⱽ : SCwFⱽ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') → SCwFᴰ S {!!} {!!} {!!} {!!}
--   SCwFⱽ→ᴰ Sⱽ .SCwFᴰ.Cᴰ = Sⱽ .SCwFⱽ.Cᴰ
--   SCwFⱽ→ᴰ Sⱽ .SCwFᴰ.Tyᴰ A = Sⱽ .SCwFⱽ.Cᴰ .Categoryᴰ.ob[_] (S.ext A (S.term .vertex) .vertex)
--   SCwFⱽ→ᴰ Sⱽ .SCwFᴰ.Tmᴰ Aᴰ = reindPshᴰNatTrans {!!} (Sⱽ .SCwFⱽ.Cᴰ [-][-, Aᴰ ])
--   SCwFⱽ→ᴰ Sⱽ .SCwFᴰ.termᴰ = {!!}
--   SCwFⱽ→ᴰ Sⱽ .SCwFᴰ.extᴰ = {!!}
  -- field
  --   -- only need universal quantifiers over ext
  --   forallⱽ : ∀ Γ A (Γᴰ : Cᴰ.ob[ ext A Γ .vertex ])
  --     → ∀FOb {!!} {!!}
  -- module Tmᴰ {A} (Aᴰ : Tyᴰ A) = PresheafᴰNotation Cᴰ (Tm A) (Tmᴰ Aᴰ)
  -- module termᴰ = UniversalElementᴰNotation {C = C} Cᴰ (UnitPsh {C = C}) (UnitPshᴰ {P = UnitPsh {C = C}}) {ue = term} termᴰ
  -- module extᴰ {A} (Aᴰ : Tyᴰ A) = isLRᴰNotation (? , ext A) (extᴰ Aᴰ)

-- SCwFⱽ : (C : SCwF ℓC ℓC' ℓT ℓT') → (ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' : Level) → Type _
-- SCwFⱽ (C , Ty , Tm , term , comprehension) ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' =
--   Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ]
--   let module Cᴰ = Categoryᴰ Cᴰ in
--   Σ[ Tyᴰ ∈ (Ty → Type ℓTᴰ) ]
--   Σ[ Tmᴰ ∈ (∀ {A} (Aᴰ : Tyᴰ A) → Presheafᴰ (Tm A) Cᴰ ℓTᴰ') ]
--   Terminalsⱽ Cᴰ ×
--   isFibration Cᴰ ×
--   BinProductsⱽ Cᴰ ×
--   (∀ {A} (Aᴰ : Tyᴰ A) → isFibrationPshᴰ (Tm A) Cᴰ (Tmᴰ Aᴰ))
--   -- we should also have pushforward along var : A ∷ · → A

-- --   do we need pushforwards along wk ?

-- -- -- A (strict) section is a section that preserves the SCwF structure on the nose
-- -- module _ (C : SCwF ℓC ℓC' ℓT ℓT') ((Cᴰ , Tyᴰ , Tmᴰ , termᴰ , comprehensionᴰ) : SCwFᴰ C ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') where
-- --   private
-- --     Tm = C .snd .snd .fst
-- --   open Section
-- --   StrictSection : Type _
-- --   StrictSection =
-- --     Σ[ F ∈ GlobalSection Cᴰ ]
-- --     Σ[ F-ty ∈ (∀ A → Tyᴰ A) ]
-- --     -- Takes a Tm A Γ to a Tmᴰ
-- --     Σ[ F-tm ∈ (∀ A → PshSection F (Tmᴰ (F-ty A))) ]
-- --     -- preserves terminal object
    
-- --     strictlyPreservesTerminal F _ termᴰ
-- --     × (∀ A → strictlyPreservesLocalRep (Tmᴰ (F-ty A) , comprehensionᴰ (F-ty A)) (F-tm A))
