{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Sum as Sum

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Free.CartesianCategory.Base as Law
open import
    Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Sets.Properties

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties

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
    t f : MOR

  discreteMOR : Discrete MOR
  discreteMOR = sectionDiscrete {A = ℕ}
    (λ { zero → t ; (suc _) → f })
    (λ { t → 0 ; f → 1 })
    (λ { t → refl ; f → refl })
    discreteℕ

  isSetMOR : isSet MOR
  isSetMOR = Discrete→isSet discreteMOR

  interleaved mutual -- not actually mutually recursive, just to interleave
    dom cod : MOR → ProdExpr OB

    dom t = ⊤
    cod t = ↑ ans

    dom f = ⊤
    cod f = ↑ ans

  QUIVER : ×Quiver _
  QUIVER .fst = OB
  QUIVER .snd .ProductQuiver.mor = MOR
  QUIVER .snd .ProductQuiver.dom = dom
  QUIVER .snd .ProductQuiver.cod = cod

  private module Q = ×QuiverNotation QUIVER

  FREECC : CartesianCategory _ _
  FREECC = FreeCartesianCategory QUIVER

  open CartesianCategoryNotation FREECC
  open Terminal'Notation CCTerminal'

  [ans] : FREECC .fst .ob
  [ans] = ↑ ans

  [t] [f] : FREECC .fst [ 𝟙 , [ans] ]
  [t] = ↑ₑ t
  [f] = ↑ₑ f

  boolToExp : Bool → FREECC .fst [ 𝟙 , [ans] ]
  boolToExp = if_then [t] else [f]

  [t]≠[f] : ¬ ([t] ≡ [f])
  [t]≠[f] p = true≢false (cong n p)
    where
    sem : Functor (FREECC .fst) (SET ℓ-zero)
    sem = Law.rec _
      (SET ℓ-zero ,
        Terminal'ToTerminal terminal'SET ,
        BinProducts'ToBinProducts _ BinProducts'SET)
      (λ { ans → Bool , isSetBool})
      λ { t → λ _ → true ; f → λ _ → false}
    n : FREECC .fst [ 𝟙 , [ans] ] → Bool
    n e = (sem ⟪ e ⟫) _

  CanonicalForm : FREECC .fst [ 𝟙 , [ans] ] → Type ℓ-zero
  CanonicalForm e = ([t] ≡ e) ⊎ ([f] ≡ e)

  isSetCanonicalForm : ∀ {e} → isSet (CanonicalForm e)
  isSetCanonicalForm {e = e} = isSet⊎
    (isProp→isSet (FREECC .fst .isSetHom [t] e))
    (isProp→isSet (FREECC .fst .isSetHom [f] e))

  canonicity : ∀ e → CanonicalForm e
  canonicity e = fixup (Canonicalize .F-homᴰ e _ _)
    where
    pts = FREECC .fst [ 𝟙 ,-]
    Canonicalize : Section pts (SETᴰ _ _)
    Canonicalize = elimLocal _
      (VerticalTerminalsSETᴰ (pts ⟅ ⊤ ⟆))
      (λ _ _ → isFib→F⟪π₁⟫* (CCBinProducts' (_ , _)) _ isFibrationSet ,
        isFib→F⟪π₂⟫* (CCBinProducts' (_ , _)) _ isFibrationSet)
      (λ _ _ → VerticalBinProds→ϕ[π₁x]∧ψ[π₂x] {F = pts} (CCBinProducts' (_ , _))
        (isFib→F⟪π₁⟫* (CCBinProducts' (_ , _)) _ isFibrationSet)
        (isFib→F⟪π₂⟫* (CCBinProducts' (_ , _)) _ isFibrationSet)
        VerticalBinProdsSETᴰ)
      (λ { ans global-ans → CanonicalForm global-ans , isSetCanonicalForm})
      λ { t global-ans → λ ⟨⟩ → inl (sym (FREECC .fst .⋆IdL _) ∙
          congS (λ x → x ⋆⟨ FREECC .fst ⟩ _) 𝟙η')
        ; f global-ans → λ ⟨⟩ → inr (sym (FREECC .fst .⋆IdL _) ∙
          congS (λ x → x ⋆⟨ FREECC .fst ⟩ _) 𝟙η') }
    fixup : ∀{e'} →
      ([t] ≡ FREECC .fst .id ⋆⟨ FREECC .fst ⟩ e') ⊎
      ([f] ≡ FREECC .fst .id ⋆⟨ FREECC .fst ⟩ e') →
      CanonicalForm e'
    fixup {e'} = Sum.elim
      (λ p → inl (p ∙ FREECC .fst .⋆IdL e'))
      (λ p → inr (p ∙ FREECC .fst .⋆IdL e'))
