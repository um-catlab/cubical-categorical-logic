{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Free.CartesianCategory.Base
open import Cubical.Categories.Instances.Free.CartesianCategory.UncurriedElim as FreeCC
open import
    Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Sets.Properties

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Displayed.Instances.Reindex.Properties

open import Cubical.Tactics.CategorySolver.Reflection

open Category
open Section

-- TODO: add an object that nothing uses, for a second example
module _ where
  data OB : Type ℓ-zero where
    ans : OB

  discreteOB : Discrete OB
  discreteOB = sectionDiscrete {A = ℕ}
    (λ _ → ans)
    (λ _ → 0)
    (λ { ans → refl })
    discreteℕ

  isSetOB : isSet OB
  isSetOB = Discrete→isSet discreteOB

  data MOR : Type ℓ-zero where
    t,f : MOR

  discreteMOR : Discrete MOR
  discreteMOR = sectionDiscrete {A = ℕ}
    (λ _ → t,f)
    (λ _ → 0)
    (λ { t,f → refl })
    discreteℕ

  isSetMOR : isSet MOR
  isSetMOR = Discrete→isSet discreteMOR

  dom cod : MOR → ProdExpr OB

  dom t,f = ⊤
  cod t,f = (↑ ans) × (↑ ans)

  QUIVER : ×Quiver _ _
  QUIVER .×Quiver.ob = OB
  QUIVER .×Quiver.Q .QuiverOver.mor = MOR
  QUIVER .×Quiver.Q .QuiverOver.dom = dom
  QUIVER .×Quiver.Q .QuiverOver.cod = cod

  private module Q = ×Quiver QUIVER

  FREECC : CartesianCategory _ _
  FREECC = FreeCartesianCategory QUIVER

  private
    module FREECC = CartesianCategory FREECC
  open TerminalNotation FREECC.term
  open BinProductsNotation FREECC.bp

  [ans] : FREECC.C .ob
  [ans] = ↑ ans

  [t] [f] : FREECC.C [ 𝟙 , [ans] ]
  [t] = (↑ₑ (t,f)) ⋆ₑ Exp.π₁
  [f] = (↑ₑ (t,f)) ⋆ₑ Exp.π₂

  [t]≠[f] : ¬ ([t] ≡ [f])
  [t]≠[f] p = true≢false (cong n p)
    where
    sem : Functor (FREECC.C) (SET ℓ-zero)
    sem = FreeCC.rec _
      SETCC
      (mkInterpᴰ (λ { ans → Bool , isSetBool })
                 (λ { t,f (lift tt) → true , false }))
    n : FREECC.C [ 𝟙 , [ans] ] → Bool
    n e = (sem ⟪ e ⟫) tt*

  CanonicalForm : FREECC.C [ 𝟙 , [ans] ] → Type ℓ-zero
  CanonicalForm e = ([t] ≡ e) ⊎ ([f] ≡ e)

  isSetCanonicalForm : ∀ {e} → isSet (CanonicalForm e)
  isSetCanonicalForm {e = e} = isSet⊎
    (isProp→isSet (FREECC.C .isSetHom [t] e))
    (isProp→isSet (FREECC.C .isSetHom [f] e))

  canonicity : ∀ e → CanonicalForm e
  canonicity e = fixup (Canonicalize .F-homᴰ e _ _)
    where
    pts = FREECC.C [ 𝟙 ,-]
    Canonicalize : Section pts (SETᴰ _ _)
    Canonicalize = elimLocal QUIVER pts EqSETᴰCCⱽ
      (mkInterpᴰ
        (λ { ans global-ans → CanonicalForm global-ans , isSetCanonicalForm })
        (λ { t,f ⟨⟩ (lift tt) →
          (inl (sym (FREECC.C .⋆IdL _)
               ∙ cong₂ (seq' (FREECC.C)) 𝟙extensionality refl
               ∙ sym (FREECC.C .⋆Assoc _ _ _)))
          , inr (sym (FREECC.C .⋆IdL _)
               ∙ cong₂ (seq' (FREECC.C)) 𝟙extensionality refl
               ∙ sym (FREECC.C .⋆Assoc _ _ _))
        }))
    fixup : ∀{e'} →
      ([t] ≡ FREECC.C .id ⋆⟨ FREECC.C ⟩ e') ⊎
      ([f] ≡ FREECC.C .id ⋆⟨ FREECC.C ⟩ e') →
      CanonicalForm e'
    fixup {e'} = Sum.elim
      (λ p → inl (p ∙ FREECC.C .⋆IdL e'))
      (λ p → inr (p ∙ FREECC.C .⋆IdL e'))
