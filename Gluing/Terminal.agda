{-# OPTIONS --lossy-unification #-}
-- Gluing for categories with a terminal object
module Gluing.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sum.Properties using (isProp⊎)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary hiding (⟪_⟫)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Free.CategoryWithTerminal as Free
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Instances.Codomain.Sets
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties

open import Gluing.Canonicity

open Category
open Section
-- t : ⊤ -> b
-- f : ⊤ -> b
-- d : ⊤ → ⊤
--
-- nothing using e

data OB : Type ℓ-zero where
  b e : OB

discreteOB : Discrete OB
discreteOB = sectionDiscrete {A = ℕ}
  (λ { zero → b ; (suc _) → e })
  (λ { b → 0 ; e → 1 })
  (λ { b → refl ; e → refl })
  discreteℕ

isSetOB : isSet OB
isSetOB = Discrete→isSet discreteOB

data MOR : Type ℓ-zero where
  t f d : MOR

discreteMOR : Discrete MOR
discreteMOR = sectionDiscrete {A = ℕ}
  (λ { zero → t ; 1 → f ; (suc (suc _)) → d })
  (λ { t → 0 ; f → 1 ; d → 2 })
  (λ { t → refl ; f → refl ; d → refl })
  discreteℕ

isSetMOR : isSet MOR
isSetMOR = Discrete→isSet discreteMOR

dom cod : MOR → Ob' OB
dom t = inr _
dom f = inr _
dom d = inr _

cod t = inl b
cod f = inl b
cod d = inr _

QUIVER : QuiverOver _ _
QUIVER .QuiverOver.mor = MOR
QUIVER .QuiverOver.dom = dom
QUIVER .QuiverOver.cod = cod

FQ = Free.FC OB QUIVER
T = (Free.FCTerminal OB QUIVER)
open TerminalNotation T

[b] : FQ .ob
[b] = inl b

[t] [f] : FQ [ 𝟙  , [b] ]
[t] = ↑ t
[f] = ↑ f

boolToExp : Bool → FQ [ 𝟙 , [b] ]
boolToExp = if_then [t] else [f]

[t]≠[f] : ¬ ([t] ≡ [f])
[t]≠[f] = λ p → true≢false (cong n p) where
  sem : Functor FQ (SET ℓ-zero)
  sem = Free.rec _ QUIVER (SET _) TerminalSET ıO λ
      { t → λ _ → true ; f → λ _ → false ; d → λ _ → tt* }
    where
    ıO : OB → hSet ℓ-zero
    ıO b = Bool , isSetBool
    ıO e = ⊥ , isProp→isSet isProp⊥

  n : FQ [ 𝟙 , [b] ] → Bool
  n exp = (sem ⟪ exp ⟫) _

CanonicalForm : FQ [ 𝟙 , [b] ] → Type _
CanonicalForm = λ e → ([t] ≡ e) ⊎ ([f] ≡ e)

isSetCanonicalForm : ∀ {e} → isSet (CanonicalForm e)
isSetCanonicalForm =
  isSet⊎ (isProp→isSet (isSetHom FQ _ _)) (isProp→isSet (isSetHom FQ _ _))

private
  Pts : Functor FQ (SET ℓ-zero)
  Pts = FQ [ 𝟙 ,-]

  open UniversalElementⱽ

  TerminalⱽSETCod' : Terminalⱽ (SETCod ℓ-zero) (Pts ⟅ 𝟙 ⟆)
  TerminalⱽSETCod' .vertexⱽ = 𝟙Cod
  TerminalⱽSETCod' .elementⱽ = tt
  TerminalⱽSETCod' .universalⱽ .fst _ = !Cod
  TerminalⱽSETCod' .universalⱽ .snd .fst _ = refl
  TerminalⱽSETCod' .universalⱽ .snd .snd = !Cod-η

  CF : FQ [ 𝟙 , [b] ] → hSet ℓ-zero
  CF exp = CanonicalForm exp , isSetCanonicalForm

  const : (g : FQ [ 𝟙 , [b] ]) (x : FQ [ 𝟙 , 𝟙 ]) → g ≡ x ⋆⟨ FQ ⟩ g
  const g x = sym (FQ .⋆IdL _) ∙ cong₂ (seq' FQ) 𝟙extensionality refl

Canonicalize : Section Pts (SETCod ℓ-zero)
Canonicalize = elimLocal _ _ _ _ TerminalⱽSETCod'
  (λ { e _ → Empty.⊥* , isProp→isSet isProp⊥*
     ; b → CF })
  λ { t → mk ℓ-zero λ z → (_ , inl (const [t] (z .fst))) , refl
    ; f → mk ℓ-zero λ z → (_ , inr (const [f] (z .fst))) , refl
    ; d → !Cod }

canonicityCod : ∀ exp → Fib ℓ-zero {Y = Pts ⟅ [b] ⟆} CF exp
canonicityCod = canonicalize 𝟙 Canonicalize tt*

canonicity : ∀ exp → CanonicalForm exp
canonicity exp = Sum.map (λ p → p ∙ canonicityCod exp .snd)
  (λ p → p ∙ canonicityCod exp .snd) (canonicityCod exp .fst .snd)

decide : FQ [ 𝟙 , [b] ] → Bool
decide exp = Sum.rec (λ _ → true) (λ _ → false) (canonicityCod exp .fst .snd)

canonicalFormUniq : ∀ exp → isContr (CanonicalForm exp)
canonicalFormUniq exp = canonicity exp , isProp⊎
  (FQ .isSetHom _ _) (FQ .isSetHom _ _) (λ p q → [t]≠[f] (p ∙ sym q)) _

private
  module Examples where
    _ : decide (((↑ d) ⋆ₑ (↑ d)) ⋆ₑ (idₑ ⋆ₑ (↑ t))) ≡ true
    _ = refl

    _ : decide (!ₑ ⋆ₑ (↑ f)) ≡ false
    _ = refl

    _ : canonicityCod (!ₑ ⋆ₑ (↑ f)) .fst .fst ≡ (idₑ ⋆ₑ !ₑ) ⋆ₑ (↑ f)
    _ = refl
