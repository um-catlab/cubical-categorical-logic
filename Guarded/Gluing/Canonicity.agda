{-

  A guarded canonicity theorem

-}
{-# OPTIONS --lossy-unification --rewriting --guarded #-}

open import Guarded.Later.Base

module Guarded.Gluing.Canonicity (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.Graph.Base as Graph
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂)
import Cubical.HITs.SetTruncation as Trunc

open import Cubical.Categories.Category.Base
open import Cubical.Categories.FixedPoint
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Fiber hiding (fiber)
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Instances.Free.Category.GuardedFixedPoint as Syn
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.FixedPoint
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration

open import Cubical.Data.Nat as Nat hiding (elim)
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory as TotalCat hiding (elim; recᴰ)
open import Cubical.Categories.Displayed.Instances.Family.Base
open import Cubical.Categories.Displayed.Instances.Family.Properties
open import Cubical.Categories.Displayed.Instances.Family.EqProperties
open import Cubical.Categories.Displayed.Instances.PropertyOver as PropertyOver
open import Cubical.Categories.Displayed.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Sets

open import Guarded.Later.Properties k

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰ'' : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level


open Category
open Categoryᴰ
open Functor
open Functorᴰ
open NatTrans
open NatTransᴰ
open PshIso
open Section
open UniversalElement

SETᴰ0 : Categoryᴰ (SET ℓ-zero) (ℓ-suc ℓ-zero) ℓ-zero
SETᴰ0 = Fam (SET ℓ-zero)

module SETᴰ0 = Fibers SETᴰ0

SETᴰ-Terminalsⱽ : Terminalsⱽ SETᴰ0
SETᴰ-Terminalsⱽ = EqTerminalsⱽ→Terminalsⱽ SetAssoc SETᴰ0
  (FamTerminalsⱽ {ℓ = ℓ-zero} (SET ℓ-zero) TerminalSET)

SETᴰ-fibration : isFibration SETᴰ0
SETᴰ-fibration = EqFibration→Fibration {C = SET ℓ-zero}
  SetAssoc
  SETᴰ0
  (isFibrationFam {ℓ = ℓ-zero} (SET ℓ-zero))

▹SET : Functor (SET ℓ-zero) (SET ℓ-zero)
▹SET .F-ob (X , isSetX) .fst = ▹ X
▹SET .F-ob (X , isSetX) .snd = isSet▹ (next isSetX)
▹SET .F-hom = λ z z₁ t → z (z₁ t)
▹SET .F-id = refl
▹SET .F-seq = λ _ _ → refl

nextAsNT : NatTrans Id ▹SET
nextAsNT .N-ob A = next
nextAsNT .N-hom = λ _ → refl

SETᴰ-Guarded : GuardedLogic (SET ℓ-zero) _ _
SETᴰ-Guarded .GuardedLogic.Cᴰ = SETᴰ0
SETᴰ-Guarded .GuardedLogic.▷ⱽ = FamF ▹SET
SETᴰ-Guarded .GuardedLogic.next = Fam-PtNT nextAsNT
SETᴰ-Guarded .GuardedLogic.isFibCᴰ = SETᴰ-fibration
SETᴰ-Guarded .GuardedLogic.termⱽ = SETᴰ-Terminalsⱽ
SETᴰ-Guarded .GuardedLogic.gfpⱽ {A = X} {Aᴰ = Xᴰ} fⱽ =
  fixed-pointⱽ'→ⱽ _ _ _ _ (subst (fixed-pointⱽ' SETᴰ0 X (SETᴰ-Terminalsⱽ X .fst))
    (SETᴰ0.rectifyOut {a = X}{b = X}{aᴰ = Xᴰ}{bᴰ = Xᴰ}{e' = refl}
     (SETᴰ0.reind-filler _))
    ((λ x tt* → fix (λ x~ → fⱽ x x~)) , (funExt (λ x → funExt (λ _ → sym (fix-eq (fⱽ x))))))
    )

module Delayᴰ {V : Type ℓ}{X : Type ℓ'} (ret : V → X) (δ : X → X) (Vᴰ : V → Type ℓᴰ) where
  -- Universal property:
  -- free SETᴰ generated by ret(Vᴰ) and closed under a θᴰ operation over δ

  data Delayᴰ : (x : X) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴰ)) where
    terminates : ∀ {v} → Vᴰ v → Delayᴰ (ret v)
    θᴰ : ∀ {x} → ▹ (Delayᴰ x) → Delayᴰ (δ x)

  isSetDelayᴰ : isSet V → (∀ v → isSet (Vᴰ v)) → isSet X → ∀ x → isSet (Delayᴰ x)
  isSetDelayᴰ isSetV isSetVᴰ isSetX = fix {k = k} λ ▹isSetDelayᴰ → λ x → isSetRetract {B = Dᴰ' x}
      (λ { (terminates x) → inl ((_ , Eq.refl) , x) ; (θᴰ x) → inr ((_ , Eq.refl) , x) })
      (λ { (inl ((_ , Eq.refl) , vᴰ)) → terminates vᴰ ; (inr ((_ , Eq.refl) , dᴰ)) → θᴰ dᴰ })
      (λ { (terminates x) → refl ; (θᴰ x) → refl })
      (isSet⊎ (isSetΣ (Eq.isSet→isSetEqFiber isSetV isSetX) (λ x₁ → isSetVᴰ (x₁ .fst)))
              (isSetΣ (Eq.isSet→isSetEqFiber isSetX isSetX) (λ x' → isSet▹ (▹Π ▹isSetDelayᴰ (x' .fst)))))
    where
    open import Cubical.Data.Sum
    Dᴰ' : X → Type _
    Dᴰ' x = (Σ[ v ∈ Eq.fiber ret x ] Vᴰ (v .fst)) ⊎ (Σ[ x' ∈ Eq.fiber δ x ] (▹ (Delayᴰ (x' .fst))))

  -- Universal element
  retᴰ : ∀ v → (Vᴰ v) → (Delayᴰ (ret v))
  retᴰ v = terminates

  module _ (Xᴰ : X → Type ℓᴰ'')
    (⟦retᴰ⟧ : ∀ v → (Vᴰ v) → (Xᴰ (ret v)))
    (⟦θᴰ⟧ : ∀ x → (▹ (Xᴰ x)) → (Xᴰ (δ x)))
    where
    recᴰ : ∀ d → Delayᴰ d → Xᴰ d
    recᴰ d (terminates vᴰ) = ⟦retᴰ⟧ _ vᴰ
    recᴰ d (θᴰ dᴰ~) = ⟦θᴰ⟧ _ (λ t → recᴰ _ (dᴰ~ t))

-- Gluing
Γ : Functor EXP (SET ℓ-zero)
Γ = EXP [ [1] ,-]

𝓖 = reindex SETᴰ0 Γ

𝓖-guardedLogic : GuardedLogic EXP _ _
𝓖-guardedLogic = reindexGuardedLogic Γ SETᴰ-Guarded

private
  module 𝓖 where
    open GuardedLogic 𝓖-guardedLogic hiding (module Cᴰ) public
    open Fibers Cᴰ public

1ᴰ𝓖 : Terminalᴰ 𝓖 [1]-TERMINAL
1ᴰ𝓖 = Terminalⱽ→ᴰ 𝓖 [1]-TERMINAL (𝓖.termⱽ (vertex [1]-TERMINAL))

can-lem : ∀ {B} (γ : Exp [1] [1]) (M : Exp [1] B) → M ≡ γ ⋆ₑ M
can-lem γ M = sym (EXP.⋆IdL _) ∙ EXP.⟨ 1ηₑ ∙ sym 1ηₑ ⟩⋆⟨ refl ⟩

open Delayᴰ {V = Bool} quoteBool (_⋆ₑ [δ]) (λ M → Unit* {ℓ = ℓ-zero})

bool-gen : ∀ b e → (Unit* {ℓ = ℓ-zero}) → (Delayᴰ (e ⋆ₑ quoteBool b))
bool-gen b e = subst (λ M → Unit* → (Delayᴰ M))
  (can-lem e (quoteBool b))
  (retᴰ b)


[RetBoolᴰ] : 𝓖.ob[ [RetBool] ]
[RetBoolᴰ] = λ x → (Delayᴰ x)
  , isSetDelayᴰ isSetBool (λ _ → isSetUnit*) isSetExp x


⟦_⟧ : ∀ B → 𝓖.ob[ B ]
⟦_⟧ = elimOb 𝓖 1ᴰ𝓖 [RetBoolᴰ]


[θᴰ] : ∀ B → 𝓖.Hom[ [δ] ][ 𝓖.▷ⱽ .F-obᴰ ⟦ B ⟧ , ⟦ B ⟧ ]
[θᴰ] [1] = λ x _ → tt*
[θᴰ] [RetBool] M = θᴰ


[δᴰ] : ∀ B → 𝓖.Hom[ [δ] ][ ⟦ B ⟧ , ⟦ B ⟧ ]
[δᴰ] B = 𝓖._⋆ⱽᴰ_ {xᴰ = ⟦ B ⟧} {xᴰ' = 𝓖.▷ⱽ .F-obᴰ ⟦ B ⟧} {yᴰ = ⟦ B ⟧}
  (𝓖.next .N-obᴰ ⟦ B ⟧)
  ([θᴰ] B)


GuardedCanonicitySection : GlobalSection 𝓖
GuardedCanonicitySection = elim 𝓖 1ᴰ𝓖
  [RetBoolᴰ]
  (λ e → bool-gen true e)
  (λ e → bool-gen false e)
  (λ {B} → [δᴰ] B)
  λ {B} {M} Mᴰ → 𝓖.gfixⱽ→ᴰ [1] B ⟦ B ⟧ [δ] M ([θᴰ] B) Mᴰ (Syn.guarded-fixed-points M)

GuardedCanonicity : ∀ (M : Exp [1] [RetBool]) → Delayᴰ M
GuardedCanonicity M =
  subst (λ M → Delayᴰ M)
  (EXP.⋆IdL M)
  (GuardedCanonicitySection .F-homᴰ M EXP.id _)

