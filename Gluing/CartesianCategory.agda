{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
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
open import Cubical.Categories.Displayed.Instances.Codomain.Sets
open import Gluing.Canonicity

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

  pts : Functor FREECC.C (SET ℓ-zero)
  pts = FREECC.C [ 𝟙 ,-]

  private
    CF : FREECC.C [ 𝟙 , [ans] ] → hSet ℓ-zero
    CF e = CanonicalForm e , isSetCanonicalForm {e = e}

    const : ∀ {o} (g : FREECC.C [ 𝟙 , o ]) (e : FREECC.C [ 𝟙 , 𝟙 ])
      → g ≡ e ⋆⟨ FREECC.C ⟩ g
    const g e =
      sym (FREECC.C .⋆IdL _) ∙ cong₂ (seq' FREECC.C) 𝟙extensionality refl

  Canonicalize : Section pts (SETCod ℓ-zero)
  Canonicalize = elimLocal QUIVER pts (SETCodCCⱽ {ℓ-zero}) (mkInterpᴰ
    (λ { ans → CF })
    (λ { t,f → mk ℓ-zero λ z →
      let p = z .fst ⋆⟨ FREECC.C ⟩ ↑ₑ t,f in
      (p , ((p , ((p ⋆⟨ FREECC.C ⟩ Exp.π₁
                  , inl (const [t] (z .fst) ∙ sym (FREECC.C .⋆Assoc _ _ _)))
                  , refl)) , refl)
         , ((p , ((p ⋆⟨ FREECC.C ⟩ Exp.π₂
                  , inr (const [f] (z .fst) ∙ sym (FREECC.C .⋆Assoc _ _ _)))
                  , refl)) , refl))
      , refl }))

  canonicityCod : ∀ e → Fib ℓ-zero {Y = pts ⟅ [ans] ⟆} CF e
  canonicityCod = canonicalize 𝟙 Canonicalize tt*

  canonicity : ∀ e → CanonicalForm e
  canonicity e = Sum.map (λ p → p ∙ canonicityCod e .snd)
    (λ p → p ∙ canonicityCod e .snd) (canonicityCod e .fst .snd)

  decide : FREECC.C [ 𝟙 , [ans] ] → Bool
  decide e = Sum.rec (λ _ → true) (λ _ → false) (canonicityCod e .fst .snd)

  private
    module Examples where
      _ : decide ((⟨ [f] , [t] ⟩ ⋆ₑ Exp.π₂) ⋆ₑ idₑ) ≡ true
      _ = refl

      _ : decide (⟨ [f] , [t] ⟩ ⋆ₑ Exp.π₁) ≡ false
      _ = refl
