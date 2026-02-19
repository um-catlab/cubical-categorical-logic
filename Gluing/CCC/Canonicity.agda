{-# OPTIONS --lossy-unification #-}
module Gluing.CCC.Canonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More

open import Cubical.Relation.Nullary hiding (⟪_⟫)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Quiver.Base

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Base
open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.UncurriedElim as FreeCCC
open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver as FreeCCC
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Sets.Properties

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Sets.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties

open Category
open Section

module _ where
  data OB : Type where
    ans : OB

  data MOR : Type ℓ-zero where
    t,f : MOR

  open QuiverOver
  QUIVER : FreeCCC.×⇒Quiver _ _
  QUIVER .×⇒Quiver.ob = OB
  QUIVER .×⇒Quiver.Q .mor = MOR
  QUIVER .×⇒Quiver.Q .dom t,f = ⊤
  QUIVER .×⇒Quiver.Q .cod t,f = ⊤ ⇒ ((↑ ans) FreeCCC.× (↑ ans))

  discreteOB : Discrete OB
  discreteOB = sectionDiscrete {A = ℕ}
    (λ _ → ans)
    (λ _ → 0)
    (λ { ans → refl })
    discreteℕ

  isSetOB : isSet OB
  isSetOB = Discrete→isSet discreteOB

  discreteMOR : Discrete MOR
  discreteMOR = sectionDiscrete {A = ℕ}
    (λ _ → t,f)
    (λ _ → 0)
    (λ { t,f → refl })
    discreteℕ

  isSetMOR : isSet MOR
  isSetMOR = Discrete→isSet discreteMOR
  private
    module Q = ×⇒Quiver QUIVER

  FREECCC : CartesianClosedCategory _ _
  FREECCC = FreeCartesianClosedCategory QUIVER

  private
    module FREECCC = CartesianClosedCategory FREECCC


  [ans] : FREECCC.ob
  [ans] = ↑ ans

  [t] [f] : FREECCC.Hom[ ⊤ , [ans] ]
  [t] = (⟨ ↑ₑ t,f , idₑ ⟩ ⋆ₑ eval) ⋆ₑ π₁
  [f] = (⟨ ↑ₑ t,f , idₑ ⟩ ⋆ₑ eval) ⋆ₑ π₂

  SET-semantics : Functor FREECCC.C (SET ℓ-zero)
  SET-semantics = FreeCCC.rec QUIVER SETCCC
    (interpᴰ (λ { ans → Bool , isSetBool })
      (λ { t,f → λ _ _ → (true , false) }))

  [t]≠[f] : ¬ ([t] ≡ [f])
  [t]≠[f] p = true≢false (cong n p)
    where
      n : FREECCC.Hom[ ⊤ , [ans] ] → Bool
      n e = (SET-semantics ⟪ e ⟫) _

  -- Canonicity: every term is equal to a standard boolean
  CanonicalForm : FREECCC.C [ ⊤ , [ans] ] → Type ℓ-zero
  CanonicalForm e = ([t] ≡ e) ⊎ ([f] ≡ e)

  isSetCanonicalForm : ∀ {e} → isSet (CanonicalForm e)
  isSetCanonicalForm {e = e} = isSet⊎
    (isProp→isSet (FREECCC.C .isSetHom [t] e))
    (isProp→isSet (FREECCC.C .isSetHom [f] e))

  Points : Functor FREECCC.C (SET ℓ-zero)
  Points = FREECCC.C [ ⊤ ,-]

  PointsCartesian : CartesianFunctor FREECCC.CC (SET ℓ-zero)
  PointsCartesian .fst = Points
  -- This should be a general theorem that co-representable functors preserve products/limits
  PointsCartesian .snd A B X = isIsoToIsEquiv
    ((λ (f , g) x → ⟨ f x , g x ⟩)
    , (λ (f , g) → ΣPathP ((funExt (λ x → ×β₁)) , (funExt λ _ → ×β₂)))
    , λ e⟨x⟩ → funExt (λ x → sym ×η))

  can-lemma0 : ∀ (γ⊤ x⊤ : FREECCC.Hom[ ⊤ , ⊤ ]) → ⟨ ↑ₑ t,f , idₑ ⟩ ≡ ⟨ γ⊤ ⋆ₑ (↑ₑ t,f) , x⊤ ⟩
  can-lemma0 x⊤ γ⊤ = cong₂ ⟨_,_⟩ (sym (FREECCC.⟨ ⊤η x⊤ ∙ sym (⊤η idₑ) ⟩⋆⟨ refl ⟩ ∙ FREECCC.⋆IdL _)) (⊤η idₑ ∙ sym (⊤η γ⊤))

  can-lemma : ∀ {R} (γ⊤ x⊤ : FREECCC.Hom[ ⊤ , ⊤ ]) (k : FREECCC.Hom[ [ans] FREECCC.× [ans] , R ])
    → ((⟨ ↑ₑ t,f , idₑ ⟩ ⋆ₑ eval) ⋆ₑ k) ≡ ((⟨ γ⊤ ⋆ₑ (↑ₑ t,f) , x⊤ ⟩ ⋆ₑ eval) ⋆ₑ k)
  can-lemma γ⊤ x⊤ k = FREECCC.⟨ FREECCC.⟨ can-lemma0 γ⊤ x⊤ ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩

  canonicalize' : ∀ e → CanonicalForm (idₑ ⋆ₑ e)
  canonicalize' e = Canonicalize .F-homᴰ e idₑ _
    where
    Canonicalize : Section Points (SETᴰ _ _)
    Canonicalize = elimLocal QUIVER PointsCartesian EqSETᴰCCCⱽ (interpᴰ
      (λ { ans e → CanonicalForm e , isSetCanonicalForm })
      (λ { t,f γ⊤ _ x⊤ _
        → (inl (can-lemma γ⊤ x⊤ π₁))
        , (inr (can-lemma γ⊤ x⊤ π₂)) }))

  canonicalize : ∀ e → CanonicalForm e
  canonicalize e = subst CanonicalForm (FREECCC.⋆IdL e) (canonicalize' e)

  -- opaque
  --   -- doesn't finish in reasonable time
  --   unfolding depReasoning.reind
  --   canonicity : Iso FREECCC.Hom[ ⊤ , [ans] ] Bool
  --   canonicity .Iso.fun e = Sum.rec (λ _ → true) (λ _ → false) (canonicalize e)
  --   canonicity .Iso.inv = λ { true → [t] ; false → [f] }
  --   canonicity .Iso.sec = λ { true → refl ; false → {!!} }
  --   canonicity .Iso.ret = {!!}
