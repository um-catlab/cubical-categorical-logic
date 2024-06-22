{-# OPTIONS --safe #-}
-- Gluing for categories with a terminal object
module Gluing.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function renaming (_∘_ to _∘f_)

open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.List.Properties as List
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit as Unit
open import Cubical.Data.Sigma
open import Cubical.Data.W.Indexed
open import Cubical.Relation.Nullary hiding (⟪_⟫)

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Constructions.Free.CategoryWithTerminal as Free
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Properties as Disp
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.HomFunctor

open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Instances.Functors.More

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
T = (Free.FCTerminal' OB QUIVER)
open Terminal'Notation T

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
  sem = Free.rec _ QUIVER (SET _) terminal'SET ıO λ
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

canonicity : ∀ e → CanonicalForm e
canonicity = λ exp → fixup (Canonicalize .F-homᴰ exp _ _)
  where
  pts = FQ [ 𝟙 ,-]

  Canonicalize : Section pts (SETᴰ _ _)
  Canonicalize = elimLocal _ _ _ _
    (VerticalTerminalsSETᴰ _)
    (λ { e _ → Empty.⊥* , isProp→isSet isProp⊥*
       ; b exp → CanonicalForm exp , isSetCanonicalForm
       })
    λ { f → λ ⟨⟩ _ → inr (sym (FQ .⋆IdL _) ∙ cong₂ (seq' FQ) 𝟙η' refl)
      ; t → λ ⟨⟩ _ → inl (sym (FQ .⋆IdL _) ∙ cong₂ (seq' FQ) 𝟙η' refl)
      ; d → λ x _ → tt* }

  fixup : ∀ {e}
        → ([t] ≡ (FQ .id ⋆⟨ FQ ⟩ e)) ⊎ ([f] ≡ (FQ .id ⋆⟨ FQ ⟩ e))
        → CanonicalForm e
  fixup =
    Sum.elim (λ p → inl (p ∙ FQ .⋆IdL _))
             (λ p → inr (p ∙ FQ .⋆IdL _))

canonicalFormUniq : ∀ e → isContr (CanonicalForm e)
canonicalFormUniq exp = canonicity exp , Sum.elim canonical[t] canonical[f]
  where
  canonical[t] : ∀ {exp} p → canonicity exp ≡ inl p
  canonical[t] p =
    J (λ exp p → canonicity exp ≡ inl p)
      (cong inl (FQ .isSetHom _ _ _ _))
      p

  canonical[f] : ∀ {exp} p → canonicity exp ≡ inr p
  canonical[f] p =
    J (λ exp p → canonicity exp ≡ inr p)
      (cong inr (FQ .isSetHom _ _ _ _))
      p
