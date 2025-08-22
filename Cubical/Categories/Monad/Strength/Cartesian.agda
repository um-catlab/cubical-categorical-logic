-- {- Strength for a monad on a cartesian category is a bit simpler
--   than for monoidal categories -}
{- Unfortunately this is very slow but lossy unification breaks it -}
module Cubical.Categories.Monad.Strength.Cartesian where

-- open import Cubical.Foundations.Prelude
-- open import Cubical.Categories.Category hiding (isIso)
-- open import Cubical.Categories.Constructions.BinProduct
-- open import Cubical.Categories.Functor
-- open import Cubical.Categories.NaturalTransformation
-- open import Cubical.Categories.Monad.Base
-- open import Cubical.Categories.Comonad.Base
-- open import Cubical.Categories.Comonad.Instances.Environment
-- open import Cubical.Categories.Limits.BinProduct
-- open import Cubical.Categories.Limits.BinProduct.More
-- open import Cubical.Categories.DistributiveLaw.ComonadOverMonad.Base
--open import
-- Cubical.Categories.DistributiveLaw.ComonadOverMonad.BiKleisli.Base
-- open import Cubical.Categories.Monad.Kleisli

-- open import Cubical.Tactics.FunctorSolver.Reflection
-- open import Cubical.Tactics.CategorySolver.Reflection

-- private
--   variable
--     ℓ ℓ' : Level

-- module _ {C : Category ℓ ℓ'} (bp : BinProducts C) (T : Monad C) where
--   open Notation C bp
--   open NatTrans
--   StrengthTrans : Type _
--   StrengthTrans = NatTrans (×pF ∘F (Id {C = C} ×F T .fst)) (T .fst ∘F ×pF)
--   open Category C
--   open Functor

--   Env' : ob → Comonad C
--   Env' Γ = Env Γ (bp Γ)

--   fix-Γ : ∀ Γ → StrengthTrans →
--     NatTrans (Env' Γ .fst ∘F T .fst) ((T .fst) ∘F Env' Γ .fst)
--   fix-Γ Γ σ .N-ob x = σ ⟦ Γ , x ⟧
--   -- This is the downside of removing the id in ×pF
--   fix-Γ Γ σ .N-hom f =
--     cong₂ _⋆_ (sym (×pF-with-agrees Γ)) refl ∙
--       σ .N-hom _ ∙ cong₂ _⋆_ refl (cong (T .fst ⟪_⟫) (×pF-with-agrees Γ))

--   Strength : Type _
--   Strength =
--     Σ[ σ ∈ StrengthTrans ]
--     ∀ Γ → IsDistributiveLaw (Env' Γ) T (fix-Γ Γ σ)

--   module _ (σ : Strength) where
--     open IsMonad (T .snd)
--     open IsComonad
--     open IsDistributiveLaw
--     strength-law : (Γ : ob) → DistributiveLaw (Env' Γ) T
--     strength-law Γ = (fix-Γ Γ (σ .fst)) , (σ .snd Γ)

--     change-of-base : ∀ {Δ Γ} (γ : Hom[ Δ , Γ ]) →
--       ComonadMorphism (strength-law Γ) (strength-law Δ)
--     change-of-base γ .fst = push bp γ
--     change-of-base γ .snd = makeNatTransPath (funExt (λ x →
--       (cong₂ _∘_ refl (cong₂ _×p_ refl (sym (T .fst .F-id))))
--       ∙ σ .fst .N-hom _ -- this doesn't work with --lossy-unification
--       ))

--     IndexedKleisli : ∀ (Γ : ob) → Category _ _
--     IndexedKleisli Γ = BiKleisli (Env' Γ) T (strength-law Γ)

--     -- I suppose this actually works for any comonad...
--     wkF : (Γ : ob) → Functor (Kleisli T) (IndexedKleisli Γ)
--     wkF Γ .F-ob x = x
--     wkF Γ .F-hom f = f ∘ Env' Γ .snd .ε ⟦ _ ⟧ -- π₂ is the counit of Env'!
--     wkF Γ .F-id = refl
--     wkF Γ .F-seq {x}{y}{z}f g =
--       -- μ ∘ T g ∘ f ∘ π₂
--       sym (⋆Assoc _ _ _)
--       -- μ ∘ T g ∘ π₂ ∘ (π₁ , f ∘ π₂)
--       ∙ cong₂ _∘_ refl
--         (sym ×β₂ ∙ (cong₂ _⋆_ refl (sym ((ε-law (strength-law Γ .snd))))))
--       ∙ lem0
--       -- μ ∘ T g ∘ T π₂ ∘ σ ∘ (π₁ , f ∘ π₂)
--       -- μ ∘ T (g ∘ π₂) ∘ σ ∘ (π₁ , f ∘ π₂)
--       ∙ cong₂ _∘_ refl
--         ((cong₂ _∘_ refl (cong₂ _,p_ (sym ×β₁) (sym (⋆IdL _) ∙
--           cong₂ _∘_ refl (sym ×β₂) ∙ ⋆Assoc _ _ _) ∙ sym ,p-natural)))
--       -- μ ∘ T (g ∘ π₂) ∘ σ ∘ (π₁ ,p f ∘ π₂ ∘ π₂ ) ∘ (π₁ , id)
--       where
--         lem0 : ((μ ⟦ _ ⟧ ∘ (T .fst ⟪ g ⟫)) ∘
--           (T .fst ⟪ Env' Γ .snd .ε ⟦ _ ⟧ ⟫ ∘ σ .fst ⟦ _ ⟧) ∘
--           (π₁ ,p (f ∘ π₂)))
--                ≡ (bp Γ (F-ob (T .fst) y)
--                  .BinProduct.univProp (bp Γ x .BinProduct.binProdPr₁)
--                    (bp Γ x .BinProduct.binProdPr₂ ⋆ f)
--                    .fst .fst ⋆ N-ob (σ .fst) (Γ , y)) ⋆ F-hom (T .fst)
--               (bp Γ y .BinProduct.binProdPr₂ ⋆ g) ⋆ N-ob
--               (IsMonad.μ (T .snd)) z
--         lem0 = solveFunctor! C C (T .fst)
