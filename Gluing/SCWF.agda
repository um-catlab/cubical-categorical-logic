{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-# OPTIONS --lossy-unification #-}
module Gluing.SCWF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function as Func

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.FinData.FinSet
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Dependent
open import Cubical.Data.FinSet

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.FinCard.Base
open import Cubical.Categories.Instances.FinCard.Properties
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.WithFamilies.Simple
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Instances.Free.Base
open import Cubical.Categories.WithFamilies.Simple.Instances.Sets
  renaming (SET to SCwFSET)
-- open import Cubical.Categories.WithFamilies.Simple.Instances.Reindex
--   renaming (reindex to reindexSCwFⱽ)
open import Cubical.Categories.WithFamilies.Simple.Instances.VerticalToDisplayed
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets

private
  variable
    ℓ : Level

-- gen : hGroupoid ℓ-zero
-- gen = Unit , λ _ _ _ _ _ _ → refl

-- module free-scwf-on-one-gen = FreeSCwF gen
-- open free-scwf-on-one-gen

-- free-scwf-on-one-gen : SCwF _ _ _ _
-- free-scwf-on-one-gen = FreeSCwF

-- open SCwFNotation free-scwf-on-one-gen
-- open TerminalNotation term
-- open Category C
-- open PshHom
-- open Section
-- open Functor
-- open Iso

-- _⊢_ : ob → Ty → Type _
-- Γ ⊢ A = ⟨ Tm A ⟅ Γ ⟆ ⟩

-- NormalForm : ∀ {Γ A} → Γ ⊢ A → Type _
-- NormalForm {Γ = Γ} M = Fin (length Γ)

-- isSetNormalForm : ∀ {Γ A} → {M : Γ ⊢ A} → isSet (NormalForm M)
-- isSetNormalForm = isFinSet→isSet isFinSetFinData

-- deBruijn→Fin : ∀ {Γ A} → Var Γ A → Fin (length Γ)
-- deBruijn→Fin vz = zero
-- deBruijn→Fin (vs v) = suc (deBruijn→Fin v)

-- Fin→deBruijn : ∀ {Γ A} → Fin (length Γ) → Var Γ A
-- Fin→deBruijn {Γ = x ∷ Γ} zero = vz
-- Fin→deBruijn {Γ = x ∷ Γ} (suc n) = vs (Fin→deBruijn n)

-- deBruijnSection : ∀ {Γ A} → section (deBruijn→Fin {Γ}{A}) Fin→deBruijn
-- deBruijnSection {Γ = x ∷ Γ} zero = refl
-- deBruijnSection {Γ = x ∷ Γ} (suc n) = cong suc (deBruijnSection n)

-- deBruijnRetract : ∀ {Γ A} → retract (deBruijn→Fin {Γ}{A}) Fin→deBruijn
-- deBruijnRetract vz = refl
-- deBruijnRetract (vs v) = cong vs (deBruijnRetract v)

-- deBruijn≅Fin : ∀ {Γ A} → Iso (Var Γ A) (Fin (length Γ))
-- deBruijn≅Fin .fun = deBruijn→Fin
-- deBruijn≅Fin .inv = Fin→deBruijn
-- deBruijn≅Fin .rightInv = deBruijnSection
-- deBruijn≅Fin .leftInv = deBruijnRetract

-- F : PreFunctor free-scwf-on-one-gen (FINSET^opSCwF ℓ-zero)
-- F .fst .F-ob Γ = mkfs (Fin (length Γ)) isFinSetFinData
-- F .fst .F-hom γ .fst n = deBruijn→Fin (ren γ (Fin→deBruijn n))
-- F .fst .F-hom γ .snd = _
-- F .fst .F-id {x = Γ} =
--   Σ≡Prop (λ _ → isPropUnit) $
--     funExt λ where
--       n →
--         cong deBruijn→Fin (renId Γ (Fin→deBruijn n))
--         ∙ deBruijnSection n
-- F .fst .F-seq γ δ =
--   Σ≡Prop (λ _ → isPropUnit) $
--     funExt λ where
--       n →
--         cong deBruijn→Fin
--           (ren⋆ δ (Fin→deBruijn n)
--            ∙ cong (ren γ)
--              (sym $ deBruijnRetract (ren δ (Fin→deBruijn n))))
-- F .snd .fst _ = mkfs Unit isFinSetUnit
-- F .snd .snd .N-ob Γ v .fst _ = deBruijn→Fin v
-- F .snd .snd .N-ob Γ v .snd = _
-- F .snd .snd .N-hom Γ Δ γ v =
--   Σ≡Prop (λ _ → isPropUnit) $
--     funExt λ _ →
--       cong (deBruijn→Fin Func.∘ (ren γ)) (sym $ deBruijnRetract _)


-- -- reindexSCwFⱽSET : SCwFⱽ free-scwf-on-one-gen _ _ _ _
-- -- reindexSCwFⱽSET =
-- --   reindexSCwFⱽ F {!!}
--   -- reindexSCwFⱽ {C = free-scwf-on-one-gen} {D = SCwFSET ℓ-zero}
--   --   F (SETⱽ _ ℓ-zero)

-- -- -- -- -- TODO elimLocal for SCwFᴰ
-- -- -- -- canonicalize :
-- -- -- --   StrictSection
-- -- -- --     free-scwf-on-one-gen
-- -- -- --     (SCwFⱽ→SCwFᴰ {Cᴰ = reindexSCwFⱽSET})
-- -- -- -- canonicalize =
-- -- -- --   elimSCwF gen
-- -- -- --     (SCwFⱽ→SCwFᴰ {Cᴰ = reindexSCwFⱽSET})
-- -- -- --     λ _ _ → Unit , isSetUnit

-- -- -- -- canonicity : ∀ {c} → (e : C [ 𝟙 , c ]) → CanonicalForm e
-- -- -- -- canonicity e = {!canonicalize .fst .F-homᴰ e !}
