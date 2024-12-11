{-

  The SCwF of sets, global sections functor, displayed SCwF of subsets, families

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.WithFamilies.Simple.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More


open import Cubical.Categories.Displayed.Instances.Sets.Base
-- open import Cubical.Categories.Displayed.Instances.Sets.Limits
open import Cubical.Categories.Displayed.Instances.Sets.Properties

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.WithFamilies.Simple.Reindex
open import Cubical.Categories.WithFamilies.Simple.FromCartesianCategory


open Category
open NatTrans
open UniversalElement

private
  variable
    ℓC ℓC' ℓT ℓT' : Level

SET-SCwF : ∀ (ℓ : Level) → SCwF (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ
SET-SCwF ℓ = CartesianCategory→SCwF
  ( SET ℓ
  , Terminal'ToTerminal terminal'SET
  , BinProducts'ToBinProducts _ BinProducts'SET)

opaque
  GlobalSections : ∀ (C : SCwF ℓC ℓC' ℓT ℓT')
   → PreMorphism C (SET-SCwF (ℓ-max ℓC' ℓT'))
  GlobalSections {ℓT' = ℓT'} (C , Ty , Tm , term , _) .fst =
    LiftF {ℓ' = ℓT'} ∘F (C [ term .fst ,-])
  GlobalSections {ℓC' = ℓC'} (C , Ty , Tm , term , _) .snd .fst A .fst =
    Lift {j = ℓC'} ⟨ Tm A ⟅ term .fst ⟆ ⟩
  GlobalSections (C , Ty , Tm , term , _) .snd .fst A .snd =
    isOfHLevelLift 2 $ str $ Tm A ⟅ term .fst ⟆
  GlobalSections (C , Ty , Tm , term , _) .snd .snd A =
    (λ Γ M γ → lift $ Tm A ⟪ γ .lower ⟫ $ M)
    , λ δ M → funExt λ γ → cong lift $ sym $
      PresheafReasoning.⋆ᴾAssoc (Tm A) (γ .lower) δ M

GlobalSectionsLR : ∀ (C : SCwF ℓC ℓC' ℓT ℓT') (ℓ : Level)
  → SCwFᴰ C _ _ _ _
GlobalSectionsLR C ℓ = SCwFⱽ→SCwFᴰ _ $
  -- TODO: make SCwF into no-eta-equality records maybe?
  reindex {C = C}{D = SET-SCwF _}
    (CartesianCategoryⱽ→SCwFⱽ {C = ( SET _
     , Terminal'ToTerminal terminal'SET
     , BinProducts'ToBinProducts _ BinProducts'SET)}
       (SETᴰCartesianCategoryⱽ _ ℓ))
    (GlobalSections C)
