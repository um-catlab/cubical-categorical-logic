module Cubical.Categories.Instances.FinOrd.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function as Func
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.SumFin
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Mod
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinOrd.Properties
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as ⊥

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Adjoint
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Equivalence.AdjointEquivalence
open import Cubical.Categories.Instances.FinOrd.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.WithFamilies.Simple
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.WithFamilies.Simple.Instances.Democratic
open import Cubical.Categories.Constructions.FullSubcategory.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.Terminal renaming (preservesTerminal to secPreservesTerminal)
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Properties

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Category
open Functor
open AdjointEquivalence
open UnitCounit
open TriangleIdentities
open UniversalElement
open CartesianCategory
open Section
open UniversalElementᴰ

module _ ℓ where
  open FullSubcategory' (SET ℓ) isFinite
  TerminalFINORD : Terminal' (FINORD ℓ)
  TerminalFINORD = ∫termFull TerminalSET (isFinOrdLift isFinOrdUnit)

  BinProductsFINORD : BinProducts (FINORD ℓ)
  BinProductsFINORD = ∫bpFull BinProductsSET
    (λ fin fin' → isFinOrd× _ fin _ fin')

  BinCoproductsFINORD : BinCoproducts (FINORD ℓ)
  BinCoproductsFINORD = ∫bcpFull BinCoproductsSET
    (λ fin fin' → isFinOrd⊎ _ fin _ fin')

  InitialFINORD : Initial (FINORD ℓ)
  InitialFINORD = ∫initFull InitialSET (isFinOrdLift isFinOrd⊥)

  FINORDCartesianCategory : CartesianCategory _ ℓ
  FINORDCartesianCategory .C = FINORD _
  FINORDCartesianCategory .term = TerminalFINORD
  FINORDCartesianCategory .bp = BinProductsFINORD

  FINORD^opCartesianCategory : CartesianCategory _ ℓ
  FINORD^opCartesianCategory .C = FINORD^op _
  FINORD^opCartesianCategory .term = InitialFINORD
  FINORD^opCartesianCategory .bp = BinCoproductsFINORD

  FINORDSCwF : SCwF (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ
  FINORDSCwF = CartesianCategory→SCwF FINORDCartesianCategory

  FINORD^opSCwF : SCwF (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ
  FINORD^opSCwF = CartesianCategory→SCwF FINORD^opCartesianCategory


  -- module isFreeSCwFFINORD^op {ℓC ℓC' ℓSᴰ ℓSᴰ'} (Sᴰ : SCwFᴰ FINORD^opSCwF ℓC ℓC' ℓSᴰ ℓSᴰ') where
  --   private
  --     module Sᴰ = SCwFᴰNotation Sᴰ
  --     module FINORD^op = SCwFNotation FINORD^opSCwF

  --   open TerminalᴰNotation _ Sᴰ.termᴰ

  --   module _ (elimTy : (A : FINORD^op.Ty) → Sᴰ.Tyᴰ A) where
  --     elimS-F-ob : ∀ Γ → Sᴰ.Cᴰ.ob[ Γ ]
  --     elimS-F-ob (Γ , zero , _) = {!𝟙ᴰ!}
  --     elimS-F-ob (Γ , suc n , _) = {!Sᴰ.extᴰ.vertexᴰ {Γᴰ = elimS-F-ob ?}{Aᴰ = elimTy ?}!}

  --     elimS-F-ob : ∀ n → Sᴰ.Cᴰ.ob[ n ]
  --     elimS-F-ob zero = 𝟙ᴰ
  --     elimS-F-ob (suc n) = Sᴰ.extᴰ.vertexᴰ {Γᴰ = elimS-F-ob n}{Aᴰ = elimTy 1}

  --     elimTm : ∀ {Γ A} (M : Γ FINORD^op.⊢ A ) → elimS-F-ob Γ Sᴰ.[ M ]⊢ᴰ elimTy A
  --     elimTm {Γ} {zero} M =
  --       Sᴰ.Tmᴰ.reind {!!} $
  --         {!!} Sᴰ.Tmᴰ.⋆ᴰ Sᴰ.extᴰ.elementᴰ .snd
  --     elimTm {Γ} {suc A} M =
  --       {!Sᴰ.Tmᴰ.reind ? $ Sᴰ.extᴰ.elementᴰ .fst Sᴰ.Tmᴰ.⋆ᴰ elimTm {Γ} {A} (M Func.∘ inr)!}
  --     -- elimTm {zero} {zero} M = {!!}
  --     -- elimTm {zero} {suc A} M = ⊥.rec (M $ inl _)
  --     -- elimTm {suc Γ} {zero} M = {!!}
  --     -- elimTm {suc Γ} {suc A} M = {!!}

  --     elimS-F-hom : ∀ {n m} →
  --       (f : FINORD^op [ n , m ]) →
  --       Sᴰ.Cᴰ [ f ][ elimS-F-ob n , elimS-F-ob m ]
  --     elimS-F-hom {m = zero} f = Sᴰ.Cᴰ.reind (funExt λ ()) (!tᴰ _)
  --     elimS-F-hom {m = suc m} f =
  --       Sᴰ.Cᴰ.reind f≡ $
  --         Sᴰ.extᴰ.introᴰ
  --           (elimS-F-hom (f Func.∘ 1,m.element .fst) ,
  --            elimTm (f Func.∘ 1,m.element .snd))
  --       where
  --       module 1,m = UniversalElementNotation (FINORD^op.ext 1 m)
  --       f≡ :
  --         1,m.intro
  --           (f Func.∘ 1,m.element .fst ,
  --            f Func.∘ 1,m.element .snd)
  --          ≡ f
  --       f≡ = 1,m.intro≡ refl


  --     -- elimS-F-hom {n = zero} {m = suc m} f = ⊥.rec (f (inl _))
  --     -- elimS-F-hom {n = suc n} {m = suc m} f = {!!}
  --     -- elimS-F-hom {zero} {zero} f = Sᴰ.Cᴰ.reind (funExt λ ()) Sᴰ.Cᴰ.idᴰ
  --     -- elimS-F-hom {suc n} {zero} f = {!!}
  --     -- elimS-F-hom {zero} {suc m} f = {!!}
  --     -- elimS-F-hom {suc n} {suc m} f = {!!}

  --     elimSection : GlobalSection Sᴰ.Cᴰ
  --     elimSection .F-obᴰ = elimS-F-ob
  --     elimSection .F-homᴰ = elimS-F-hom
  --     elimSection .F-idᴰ = {!!}
  --     elimSection .F-seqᴰ = {!!}

  --     elimPshSection :
  --       (A : FINORD^op.Ty) →
  --       PshSection elimSection (Sᴰ.Tmᴰ $ elimTy A)
  --     elimPshSection = {!!}

  --     elimPreservesTerminal : secPreservesTerminal elimSection InitialFINORD
  --     elimPreservesTerminal = {!!}

  --     elimPreservesExt : (A : FINORD^op.Ty) →
  --       preservesLocalRep ((Sᴰ.Tmᴰ $ elimTy A) , Sᴰ.extᴰ (elimTy A)) (elimPshSection A)
  --     elimPreservesExt = {!!}

  --     elimSCwFSection : SCwFSection FINORD^opSCwF Sᴰ
  --     elimSCwFSection = {!!}


  -- isFreeSCwFFINORD^op : isFreeSCwF FINORD^opSCwF
  -- isFreeSCwFFINORD^op Sᴰ = {!!}
