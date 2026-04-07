{-

  A guarded canonicity theorem

-}
{-# OPTIONS --lossy-unification --rewriting --guarded #-}

open import Guarded.Later

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
-- open import Cubical.Categories.Instances.ωSet as ωSet
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

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰ'' : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level


private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

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
  -- this is insanely slow without lossy-unification. Why?
  (isFibrationFam {ℓ = ℓ-zero} (SET ℓ-zero))



▹SET : Functor (SET ℓ-zero) (SET ℓ-zero)
▹SET .F-ob (X , isSetX) .fst = ▹ X
▹SET .F-ob (X , isSetX) .snd = {!!}
▹SET .F-hom = {!!}
▹SET .F-id = {!!}
▹SET .F-seq = {!!}

nextAsNT : NatTrans Id ▹SET
nextAsNT .N-ob A = next
nextAsNT .N-hom = {!!}

ωSETᴰ-Guarded : GuardedLogic (SET ℓ-zero) _ _
ωSETᴰ-Guarded .GuardedLogic.Cᴰ = SETᴰ0
ωSETᴰ-Guarded .GuardedLogic.▷ⱽ = FamF ▹SET
ωSETᴰ-Guarded .GuardedLogic.next = Fam-PtNT nextAsNT
ωSETᴰ-Guarded .GuardedLogic.isFibCᴰ = SETᴰ-fibration
ωSETᴰ-Guarded .GuardedLogic.termⱽ = SETᴰ-Terminalsⱽ
-- ωSETᴰ-Guarded .GuardedLogic.gfpⱽ {A = X} {Aᴰ = Xᴰ} fⱽ .fst x tt* = fix (λ x~ → fⱽ x x~)
-- ωSETᴰ-Guarded .GuardedLogic.gfpⱽ {A = X} {Aᴰ = Xᴰ} fⱽ .snd = {!!}
ωSETᴰ-Guarded .GuardedLogic.gfpⱽ {A = X} {Aᴰ = Xᴰ} fⱽ =
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
    θᴰ : ∀ {x} → ▹ Delayᴰ x → Delayᴰ (δ x)

-- module Delayᴰ {V : Type ℓ}{X : Type ℓ'} (ret : V → X) (δ : X → X) (Vᴰ : V → ωType ℓᴰ) where
--   -- Universal property:
--   -- free ωSETᴰ generated by ret(Vᴰ) and closed under a θᴰ operation over δ
--   data |Delayᴰ| : (x : X) → ℕ → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴰ)) where
--     terminates : ∀ {v n} → Vᴰ v .fst n → |Delayᴰ| (ret v) n
--     timeout : ∀ {x}                → |Delayᴰ| (δ x) 0
--     steps : ∀ {x n} → |Delayᴰ| x n → |Delayᴰ| (δ x) (suc n)

{-

  isSet|Delayᴰ| :
    isSet X
    → isSet V
    → (∀ v n → isSet (Vᴰ v .fst n))
    → ∀ x n → isSet (|Delayᴰ| x n)
  isSet|Delayᴰ| isSetX isSetV isωSetᴰVᴰ = λ x n →
    isSetRetract {B = Dᴰ (x , n)} enc dec dec∘enc≡id isSetDᴰ
    where
    open import Cubical.Data.W.Indexed
    open import Cubical.Data.Sum as Sum
    open import Cubical.Data.Empty as Empty
    Dᴰ : (X × ℕ) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴰ))
    Dᴰ = IW
      (λ (x , n) →
        (Σ[ v ∈ Eq.fiber ret x ] Vᴰ (v .fst) .fst n)
        ⊎ (Eq.fiber δ x × ((n Eq.≡ 0) ⊎ Eq.fiber suc n)))
      (λ { (x , n) (inl (ret⁻x , vᴰ)) → ⊥*
        ; (x , n) (inr (δ⁻x , inl n≡0)) → ⊥*
        ; (x , n) (inr (δ⁻x , inr suc⁻n)) → Unit
        })
      λ { (x , n) (inr (δ⁻x , inr suc⁻n)) tt → (δ⁻x .fst) , (suc⁻n .fst) }

    enc : ∀ {x n} → |Delayᴰ| x n → Dᴰ (x , n)
    enc (terminates vᴰ) = node (inl ((_ , Eq.refl) , vᴰ)) λ ()
    enc timeout = node (inr ((_ , Eq.refl) , (inl Eq.refl))) (λ ())
    enc (steps d) = node (inr ((_ , Eq.refl) , (inr (_ , Eq.refl)))) (λ _ → enc d)

    dec : ∀ {x n} → Dᴰ (x , n) → |Delayᴰ| x n
    dec (node (inl ((_ , Eq.refl) , vᴰ)) _) = terminates vᴰ
    dec (node (inr ((_ , Eq.refl) , inl Eq.refl)) _) = timeout
    dec (node (inr ((_ , Eq.refl) , inr (n , Eq.refl))) dᴰ) = steps (dec (dᴰ _))

    dec∘enc≡id : ∀ {x n} (dᴰ : |Delayᴰ| x n) → dec (enc dᴰ) ≡ dᴰ
    dec∘enc≡id (terminates x) = refl
    dec∘enc≡id timeout = refl
    dec∘enc≡id (steps dᴰ) = cong steps (dec∘enc≡id dᴰ)

    isSetDᴰ : ∀ {x n} → isSet (Dᴰ (x , n))
    isSetDᴰ = isOfHLevelSuc-IW 1
      (λ (x , n) →
        isSet⊎
          (isSetΣ (Eq.isSet→isSetEqFiber isSetV isSetX)
            (λ x₂ → isωSetᴰVᴰ (x₂ .fst) n))
          (isSet× (Eq.isSet→isSetEqFiber isSetX isSetX)
            (isSet⊎ (isProp→isSet (Eq.isSet→isSetEq isSetℕ))
              (Eq.isSet→isSetEqFiber isSetℕ isSetℕ)))) _

-}

{-
  π-Delayᴰ : ∀ {x} n → |Delayᴰ| x (suc n) → |Delayᴰ| x n
  π-Delayᴰ n (terminates x) = terminates (Vᴰ _ .snd n x)
  π-Delayᴰ zero (steps d) = timeout
  π-Delayᴰ (suc n) (steps d) = steps (π-Delayᴰ n d)

  Delayᴰ : X → ωType _
  Delayᴰ x .fst n = |Delayᴰ| x n
  Delayᴰ x .snd = π-Delayᴰ

  θᴰ : ∀ x → ωHom (▷ (Delayᴰ x)) (Delayᴰ (δ x))
  θᴰ x .fst zero (lift tt) = timeout
  θᴰ x .fst (suc n)        = steps
  θᴰ x .snd zero _ _ _ = refl
  θᴰ x .snd (suc n) d⟨sn⟩ d⟨n⟩ πd⟨sn⟩≡d⟨n⟩ i = steps (πd⟨sn⟩≡d⟨n⟩ i)

-}

  -- Universal element
  retᴰ : ∀ v → (Vᴰ v) → (Delayᴰ (ret v))
  retᴰ v = terminates


  module _ (Xᴰ : X → Type ℓᴰ'')
    (⟦retᴰ⟧ : ∀ v → (Vᴰ v) → (Xᴰ (ret v)))
    (⟦θᴰ⟧ : ∀ x → (▹ (Xᴰ x)) → (Xᴰ (δ x)))
    where

    recᴰ : ∀ d → (Delayᴰ d) → (Xᴰ d)
    recᴰ d (terminates vᴰ) = ⟦retᴰ⟧ _ vᴰ
    recᴰ d (θᴰ dᴰ~) = ⟦θᴰ⟧ _ (λ t → recᴰ _ (dᴰ~ t))



-- Gluing
Γ : Functor EXP (SET ℓ-zero)
Γ = EXP [ [1] ,-]

𝓖 = reindex SETᴰ0 Γ



𝓖-guardedLogic : GuardedLogic EXP _ _
𝓖-guardedLogic = reindexGuardedLogic Γ ωSETᴰ-Guarded


private
  module 𝓖 where
    open GuardedLogic 𝓖-guardedLogic hiding (module Cᴰ) public
    open Fibers Cᴰ public



1ᴰ𝓖 : Terminalᴰ 𝓖 [1]-TERMINAL
1ᴰ𝓖 = Terminalⱽ→ᴰ 𝓖 [1]-TERMINAL (𝓖.termⱽ (vertex [1]-TERMINAL))

can-lem : ∀ {B} (γ : Exp [1] [1]) (M : Exp [1] B) → M ≡ γ ⋆ₑ M
can-lem γ M = sym (EXP.⋆IdL _) ∙ EXP.⟨ 1ηₑ ∙ sym 1ηₑ ⟩⋆⟨ refl ⟩



--TODO: cleanup
open Delayᴰ {V = Bool} quoteBool (_⋆ₑ [δ]) (λ M → Unit* {ℓ = ℓ-zero})


bool-gen : ∀ b e → (Unit* {ℓ = ℓ-zero}) → (Delayᴰ (e ⋆ₑ quoteBool b))
bool-gen b e = subst (λ M → Unit* → (Delayᴰ M))
  (can-lem e (quoteBool b))
  (retᴰ b)


[RetBoolᴰ] : 𝓖.ob[ [RetBool] ]
[RetBoolᴰ] = λ x → (Delayᴰ x)
  , {!!} -- (isSet|Delayᴰ| isSetExp isSetBool (λ _ _ → isSetUnit*) x)


⟦_⟧ : ∀ B → 𝓖.ob[ B ]
⟦_⟧ = elimOb 𝓖 1ᴰ𝓖 [RetBoolᴰ]


[θᴰ] : ∀ B → 𝓖.Hom[ [δ] ][ 𝓖.▷ⱽ .F-obᴰ ⟦ B ⟧ , ⟦ B ⟧ ]
[θᴰ] [1] = λ x _ → tt* -- λ _ → UniversalElementNotation.intro Unit*-Terminal {c = ▷ωSet (⟦ [1] ⟧ idₑ)} tt
[θᴰ] [RetBool] M = θᴰ -- θᴰ


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


