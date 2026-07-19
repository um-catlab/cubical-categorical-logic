{-

  The guarded canonicity theorem, with the step-indexed semantics given
  by presheaves on ω — the direct-category Löb framework instantiated
  at ℕDirect — in place of the hand-rolled ωSets of
  Gluing.Category.GuardedFixedPoint.

-}
{-# OPTIONS --lossy-unification #-}
module Gluing.Category.GuardedFixedPoint.Direct where

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
open import Cubical.Data.Sum as Sum using (inl ; inr)
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Data.Nat as Nat hiding (elim)
open import Cubical.Data.Nat.Order.Recursive as R using ()
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.FixedPoint
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Fiber hiding (fiber)
open import Cubical.Categories.Instances.Free.Category.GuardedFixedPoint as Syn
open import Cubical.Categories.Limits.Terminal as Term
open import Cubical.Categories.Limits.Terminal.More as Term
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Direct.Instances.Nat
  using (ℕWFOrder ; ℕCat ; ℕDirect)
open import Cubical.Categories.Direct.StrictDownset as SD
  using (↡Psh ; ▷Psh ; next ; löb ; löb-fix ; ▷ ; nextNT)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.FixedPoint
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Instances.TotalCategory as TotalCat
  hiding (elim; recᴰ)
open import Cubical.Categories.Displayed.Instances.Family.Base
open import Cubical.Categories.Displayed.Instances.Family.Properties
open import Cubical.Categories.Displayed.Instances.Family.EqProperties
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Sets

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open NatTrans
open NatTransᴰ
open PshHomStrict
open Section
open UniversalElement

PSHω : Category (ℓ-suc ℓ-zero) ℓ-zero
PSHω = PRESHEAF ℕCat ℓ-zero

PSHω-Terminal : Terminal' PSHω
PSHω-Terminal = PSH1 ℕCat ℓ-zero

module _ {P : Presheaf ℕCat ℓ-zero}
         (f : PshHomStrict (▷Psh ℕDirect P) P) where
  private
    !* : PSHω [ Unit*Psh , UnitPsh ]
    !* .N-ob _ _ = tt
    !* .N-hom _ _ _ _ _ _ = refl

  gfixω : PSHω [ Unit*Psh , P ]
  gfixω = !* ⋆PshHomStrict löb ℕDirect P f

  guarded-fixed-pointsω :
    fixed-point PSHω Unit*Psh {x = P}
      (next ℕDirect P ⋆PshHomStrict f)
  guarded-fixed-pointsω .fst = gfixω
  guarded-fixed-pointsω .snd =
    cong (!* ⋆PshHomStrict_) (sym (löb-fix ℕDirect P f))

-- the displayed family stack over SET
PSHωᴰ0 : Categoryᴰ (SET ℓ-zero) (ℓ-suc ℓ-zero) ℓ-zero
PSHωᴰ0 = Fam PSHω

module PSHωᴰ0 = Fibers PSHωᴰ0

PSHωᴰ-Terminalsⱽ : Terminalsⱽ PSHωᴰ0
PSHωᴰ-Terminalsⱽ = EqTerminalsⱽ→Terminalsⱽ SetAssoc PSHωᴰ0
  (FamTerminalsⱽ {ℓ = ℓ-zero} PSHω PSHω-Terminal)

PSHωᴰ-fibration : isFibration PSHωᴰ0
PSHωᴰ-fibration = EqFibration→Fibration {C = SET ℓ-zero}
  SetAssoc
  PSHωᴰ0
  (isFibrationFam {ℓ = ℓ-zero} PSHω)

PSHωᴰ-Guarded : GuardedLogic (SET ℓ-zero) _ _
PSHωᴰ-Guarded .GuardedLogic.Cᴰ = PSHωᴰ0
PSHωᴰ-Guarded .GuardedLogic.▷ⱽ = FamF (▷ ℕDirect)
PSHωᴰ-Guarded .GuardedLogic.next = Fam-PtNT (nextNT ℕDirect)
PSHωᴰ-Guarded .GuardedLogic.isFibCᴰ = PSHωᴰ-fibration
PSHωᴰ-Guarded .GuardedLogic.termⱽ = PSHωᴰ-Terminalsⱽ
PSHωᴰ-Guarded .GuardedLogic.gfpⱽ {A = X}{Aᴰ = Xᴰ} fⱽ =
  fixed-pointⱽ'→ⱽ _ _ _ _
    (subst (fixed-pointⱽ' PSHωᴰ0 X (PSHωᴰ-Terminalsⱽ X .fst))
      (PSHωᴰ0.rectifyOut {a = X}{b = X}{aᴰ = Xᴰ}{bᴰ = Xᴰ}{e' = refl}
        (PSHωᴰ0.reind-filler _))
      ((λ x → gfixω (fⱽ x))
      , (funExt (λ x → guarded-fixed-pointsω (fⱽ x) .snd))))

-- the delay predicate, as a presheaf on ω
module DelayPshᴰ {V : Type ℓ}{X : Type ℓ'} (ret : V → X) (δ : X → X)
                 (Vᴰ : V → Presheaf ℕCat ℓᴰ) where

  data |Delayᴰ| : (x : X) → ℕ → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴰ)) where
    terminates : ∀ {v n} → ⟨ Vᴰ v .F-ob n ⟩ → |Delayᴰ| (ret v) n
    timeout : ∀ {x}                → |Delayᴰ| (δ x) 0
    steps : ∀ {x n} → |Delayᴰ| x n → |Delayᴰ| (δ x) (suc n)

  isSet|Delayᴰ| :
    isSet X
    → isSet V
    → ∀ x n → isSet (|Delayᴰ| x n)
  isSet|Delayᴰ| isSetX isSetV = λ x n →
    isSetRetract {B = Dᴰ (x , n)} enc dec dec∘enc≡id isSetDᴰ
    where
    open import Cubical.Data.W.Indexed
    Dᴰ : (X × ℕ) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓᴰ))
    Dᴰ = IW
      (λ (x , n) →
        (Σ[ v ∈ Eq.fiber ret x ] ⟨ Vᴰ (v .fst) .F-ob n ⟩)
        Sum.⊎ (Eq.fiber δ x × ((n Eq.≡ 0) Sum.⊎ Eq.fiber suc n)))
      (λ { (x , n) (inl (ret⁻x , vᴰ)) → ⊥*
        ; (x , n) (inr (δ⁻x , inl n≡0)) → ⊥*
        ; (x , n) (inr (δ⁻x , inr suc⁻n)) → Unit
        })
      λ { (x , n) (inr (δ⁻x , inr suc⁻n)) tt → (δ⁻x .fst) , (suc⁻n .fst) }
      where open Empty using (⊥*)

    enc : ∀ {x n} → |Delayᴰ| x n → Dᴰ (x , n)
    enc (terminates vᴰ) = node (inl ((_ , Eq.refl) , vᴰ)) λ ()
    enc timeout = node (inr ((_ , Eq.refl) , (inl Eq.refl))) (λ ())
    enc (steps d) =
      node (inr ((_ , Eq.refl) , (inr (_ , Eq.refl)))) (λ _ → enc d)

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
        Sum.isSet⊎
          (isSetΣ (Eq.isSet→isSetEqFiber isSetV isSetX)
            (λ x₂ → Vᴰ (x₂ .fst) .F-ob n .snd))
          (isSet× (Eq.isSet→isSetEqFiber isSetX isSetX)
            (Sum.isSet⊎ (isProp→isSet (Eq.isSet→isSetEq isSetℕ))
              (Eq.isSet→isSetEqFiber isSetℕ isSetℕ)))) _

  -- one-step restriction
  π1 : ∀ {x} n → |Delayᴰ| x (suc n) → |Delayᴰ| x n
  π1 n (terminates {v} vᴰ) =
    terminates (Vᴰ v .F-hom (inl (R.≤-refl n)) vᴰ)
  π1 zero (steps d) = timeout
  π1 (suc n) (steps d) = steps (π1 n d)

  private
    hom≤ : ∀ {m n} → m R.≤ n → ℕCat [ m , n ]
    hom≤ le = Sum.map (λ z → z) Eq.pathToEq (R.≤-split le)

    hom→≤R : ∀ {m n} → ℕCat [ m , n ] → m R.≤ n
    hom→≤R {m} {n} (inl m<n) = R.<-weaken {m} {n} m<n
    hom→≤R {m} (inr Eq.refl) = R.≤-refl m

    isPropHomℕ : ∀ {m n} → isProp (ℕCat [ m , n ])
    isPropHomℕ = WFOrder.isProp≤ ℕWFOrder

  -- iterated restriction along any hom of ω
  π* : ∀ {x m n} → ℕCat [ m , n ] → |Delayᴰ| x n → |Delayᴰ| x m
  π* (inr Eq.refl) d = d
  π* {m = m} {n = zero}  (inl m<0)  d = Empty.rec m<0
  π* {m = m} {n = suc n} (inl m<sn) d = π* (hom≤ {m} {n} m<sn) (π1 n d)

  π*-irr : ∀ {x m n} (p q : ℕCat [ m , n ]) (d : |Delayᴰ| x n)
         → π* p d ≡ π* q d
  π*-irr p q d = cong (λ p → π* p d) (isPropHomℕ p q)

  π*-comp : ∀ {x k m n} (g : ℕCat [ m , n ]) (h : ℕCat [ k , m ])
            (d : |Delayᴰ| x n)
          → π* (h ⋆⟨ ℕCat ⟩ g) d ≡ π* h (π* g d)
  π*-comp (inr Eq.refl) h d =
    π*-irr (h ⋆⟨ ℕCat ⟩ inr Eq.refl) h d
  π*-comp {k = k} {m = m} {n = zero} (inl m<0) h d = Empty.rec m<0
  π*-comp {k = k} {m = m} {n = suc n} (inl m<sn) h d =
    π*-irr (h ⋆⟨ ℕCat ⟩ inl m<sn) (inl κ) d
    ∙ π*-irr (hom≤ {k} {n} κ) (h ⋆⟨ ℕCat ⟩ hom≤ {m} {n} m<sn) (π1 n d)
    ∙ π*-comp (hom≤ {m} {n} m<sn) h (π1 n d)
    where
      κ : k R.< suc n
      κ = R.≤-trans {k} {m} {n} (hom→≤R h) m<sn

  private
    isProp↡ω : ∀ n y → isProp ⟨ ↡Psh ℕDirect n .F-ob y ⟩
    isProp↡ω n y = isPropΣ isPropHomℕ (λ _ → R.isProp≤)

  π*-suc : ∀ {x} n (d : |Delayᴰ| x (suc n))
         → π* (inl (R.≤-refl n)) d ≡ π1 n d
  π*-suc n d =
    π*-irr (hom≤ (R.≤-refl n)) (inr Eq.refl) (π1 n d)

  module _ (isSetX : isSet X) (isSetV : isSet V) where
    Delayᴰ : X → Presheaf ℕCat (ℓ-max ℓ (ℓ-max ℓ' ℓᴰ))
    Delayᴰ x .F-ob n = |Delayᴰ| x n , isSet|Delayᴰ| isSetX isSetV x n
    Delayᴰ x .F-hom g = π* g
    Delayᴰ x .F-id = refl
    Delayᴰ x .F-seq g h = funExt (π*-comp g h)

    private
      θ-ob : ∀ x n → ⟨ ▷Psh ℕDirect (Delayᴰ x) .F-ob n ⟩
           → |Delayᴰ| (δ x) n
      θ-ob x zero    β = timeout
      θ-ob x (suc n) β = steps (β .N-ob n (inl (R.≤-refl n) , R.≤-refl n))

      ▷restr : ∀ x {m n} → ℕCat [ m , n ]
             → ⟨ ▷Psh ℕDirect (Delayᴰ x) .F-ob n ⟩
             → ⟨ ▷Psh ℕDirect (Delayᴰ x) .F-ob m ⟩
      ▷restr x h = ▷Psh ℕDirect (Delayᴰ x) .F-hom h

      restr₂ : ∀ x {k m n} (g : ℕCat [ k , m ]) (f : ℕCat [ m , n ])
               (h : ℕCat [ k , n ]) (β : ⟨ ▷Psh ℕDirect (Delayᴰ x) .F-ob n ⟩)
             → ▷restr x g (▷restr x f β) ≡ ▷restr x h β
      restr₂ x g f h β = makePshHomStrictPath (funExt λ y → funExt λ w →
        cong (β .N-ob y) (isProp↡ω _ y _ _))

      π1-θ : ∀ x n (β : ⟨ ▷Psh ℕDirect (Delayᴰ x) .F-ob (suc n) ⟩)
           → π1 n (θ-ob x (suc n) β)
             ≡ θ-ob x n (▷restr x (inl (R.≤-refl n)) β)
      π1-θ x zero    β = refl
      π1-θ x (suc n) β = cong steps
        ( sym (π*-suc n (β .N-ob (suc n)
            (inl (R.≤-refl (suc n)) , R.≤-refl (suc n))))
        ∙ β .N-hom n (suc n) (inl (R.≤-refl n)) _ _ refl
        ∙ cong (β .N-ob n) (isProp↡ω (suc (suc n)) n _ _) )

      θ-nat : ∀ x {m n} (h : ℕCat [ m , n ])
              (β : ⟨ ▷Psh ℕDirect (Delayᴰ x) .F-ob n ⟩)
            → π* h (θ-ob x n β) ≡ θ-ob x m (▷restr x h β)
      θ-nat x (inr Eq.refl) β =
        sym (cong (θ-ob x _)
          (funExt⁻ (▷Psh ℕDirect (Delayᴰ x) .F-id) β))
      θ-nat x {m} {zero}  (inl m<0)  β = Empty.rec m<0
      θ-nat x {m} {suc n} (inl m<sn) β =
        cong (π* (hom≤ {m} {n} m<sn)) (π1-θ x n β)
        ∙ θ-nat x (hom≤ {m} {n} m<sn) (▷restr x (inl (R.≤-refl n)) β)
        ∙ cong (θ-ob x m)
            (restr₂ x (hom≤ {m} {n} m<sn) (inl (R.≤-refl n)) (inl m<sn) β)

    θᴰ : ∀ x → PshHomStrict (▷Psh ℕDirect (Delayᴰ x)) (Delayᴰ (δ x))
    θᴰ x .N-ob = θ-ob x
    θᴰ x .N-hom m n h β' β e = θ-nat x h β' ∙ cong (θ-ob x m) e

    private
      π*-term : ∀ {v m n} (h : ℕCat [ m , n ]) (vᴰ : ⟨ Vᴰ v .F-ob n ⟩)
              → π* h (terminates vᴰ) ≡ terminates (Vᴰ v .F-hom h vᴰ)
      π*-term (inr Eq.refl) vᴰ =
        sym (cong terminates (funExt⁻ (Vᴰ _ .F-id) vᴰ))
      π*-term {m = m} {n = zero}  (inl m<0)  vᴰ = Empty.rec m<0
      π*-term {v} {m} {suc n} (inl m<sn) vᴰ =
        π*-term (hom≤ {m} {n} m<sn) (Vᴰ v .F-hom (inl (R.≤-refl n)) vᴰ)
        ∙ cong terminates
            ( sym (funExt⁻
                (Vᴰ v .F-seq (inl (R.≤-refl n)) (hom≤ {m} {n} m<sn)) vᴰ)
            ∙ cong (λ z → Vᴰ v .F-hom z vᴰ) (isPropHomℕ _ _) )

    retᴰ : ∀ v → PshHomStrict (Vᴰ v) (Delayᴰ (ret v))
    retᴰ v .N-ob n = terminates
    retᴰ v .N-hom m n h vᴰ' vᴰ e = π*-term h vᴰ' ∙ cong terminates e

-- Gluing
Γ : Functor EXP (SET ℓ-zero)
Γ = EXP [ [1] ,-]

𝓖 = reindex PSHωᴰ0 Γ

𝓖-guardedLogic : GuardedLogic EXP _ _
𝓖-guardedLogic = reindexGuardedLogic Γ PSHωᴰ-Guarded

private
  module 𝓖 where
    open GuardedLogic 𝓖-guardedLogic hiding (module Cᴰ) public
    open Fibers Cᴰ public

1ᴰ𝓖 : Terminalᴰ 𝓖 [1]-TERMINAL
1ᴰ𝓖 = Terminalⱽ→ᴰ 𝓖 [1]-TERMINAL (𝓖.termⱽ (vertex [1]-TERMINAL))

can-lem : ∀ {B} (γ : Exp [1] [1]) (M : Exp [1] B) → M ≡ γ ⋆ₑ M
can-lem γ M = sym (EXP.⋆IdL _) ∙ EXP.⟨ 1ηₑ ∙ sym 1ηₑ ⟩⋆⟨ refl ⟩

Unit*ω : Presheaf ℕCat ℓ-zero
Unit*ω = Unit*Psh

open DelayPshᴰ {V = Bool} quoteBool (_⋆ₑ [δ]) (λ _ → Unit*ω)

DelayP : Exp [1] [RetBool] → Presheaf ℕCat ℓ-zero
DelayP = Delayᴰ isSetExp isSetBool

bool-gen : ∀ b e → PSHω [ Unit*ω , DelayP (e ⋆ₑ quoteBool b) ]
bool-gen b e = subst (λ M → PSHω [ Unit*ω , DelayP M ])
  (can-lem e (quoteBool b))
  (retᴰ isSetExp isSetBool b)

[RetBoolᴰ] : 𝓖.ob[ [RetBool] ]
[RetBoolᴰ] = DelayP

⟦_⟧ : ∀ B → 𝓖.ob[ B ]
⟦_⟧ = elimOb 𝓖 1ᴰ𝓖 [RetBoolᴰ]

[θᴰ] : ∀ B → 𝓖.Hom[ [δ] ][ 𝓖.▷ⱽ .F-obᴰ ⟦ B ⟧ , ⟦ B ⟧ ]
[θᴰ] [1] = λ _ → UniversalElementNotation.intro PSHω-Terminal
  {c = ▷Psh ℕDirect (⟦ [1] ⟧ idₑ)} tt
[θᴰ] [RetBool] = θᴰ isSetExp isSetBool

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
  λ {B} {M} Mᴰ → 𝓖.gfixⱽ→ᴰ [1] B ⟦ B ⟧ [δ] M ([θᴰ] B) Mᴰ
    (Syn.guarded-fixed-points M)

GuardedCanonicity : ∀ (M : Exp [1] [RetBool]) n → |Delayᴰ| M n
GuardedCanonicity M n = subst (λ M → |Delayᴰ| M n)
  (EXP.⋆IdL M)
  (GuardedCanonicitySection .F-homᴰ M EXP.id .N-ob n tt*)
