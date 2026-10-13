-- Gluing for categories with a terminal object
module Gluing.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary hiding (⟪_⟫)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Free.CategoryWithTerminal as Free
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties as SETᴰ
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties

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

