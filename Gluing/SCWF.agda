{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-# OPTIONS --lossy-unification #-}
module Gluing.SCWF where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.FinData.FinSet
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Dependent
open import Cubical.Data.FinSet

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.FinSets
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.WithFamilies.Simple
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Instances.Free.Base
  renaming (elim to elimSCwF)
open import Cubical.Categories.WithFamilies.Simple.Instances.Sets
  renaming (SET to SCwFSET)
open import Cubical.Categories.WithFamilies.Simple.Instances.Reindex
  renaming (reindex to reindexSCwFⱽ)
open import Cubical.Categories.WithFamilies.Simple.Instances.VerticalToDisplayed
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets

gen : hGroupoid ℓ-zero
gen = Unit , λ _ _ _ _ _ _ → refl

free-scwf-on-one-gen : SCwF _ _ _ _
free-scwf-on-one-gen = FreeSCwF gen

open SCwFNotation free-scwf-on-one-gen
open TerminalNotation term
open Category C
open PshHom
open Section
open Functor

CanonicalForm : ∀ {c : ob} → C [ 𝟙 , c ] → Type _
CanonicalForm e = ℕ

isSetCanonicalForm : ∀ {c} {e : C [ 𝟙 , c ]} → isSet (CanonicalForm e)
isSetCanonicalForm = isSetℕ

SCwFᴰSET : SCwFᴰ (SCwFSET ℓ-zero) _ _ _ _
SCwFᴰSET = SCwFⱽ→SCwFᴰ {C = SCwFSET _} {Cᴰ = SETⱽ _ ℓ-zero}

-- The position of a variable in context
idx : ∀ {Γ A} → Var gen Γ A → Fin (length Γ)
idx vz = zero
idx (vs v) = suc (idx v)

lengthP : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} {as : List A}
  → ListP B as → ℕ
lengthP [] = 0
lengthP (b ∷ bs) = suc (lengthP bs)

lengthP-≡ : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB} {as : List A}
  → (bs : ListP B as) → lengthP bs ≡ length as
lengthP-≡ {as = []} [] = refl
lengthP-≡ {as = a ∷ as} (b ∷ bs) = cong suc (lengthP-≡ bs)

F : PreFunctor free-scwf-on-one-gen FINSET^opSCwF
F .fst .F-ob Γ = mkfs (Fin (length Γ)) isFinSetFinData
F .fst .F-hom γ .fst x = idx (lookupP γ x)
F .fst .F-hom γ .snd = _
F .fst .F-id {x = Γ} =
  Σ≡Prop (λ _ → isPropUnit)
    (funExt λ where n → {!!})
  where
  wkRen-lem : ∀ {Γ Δ} → (γ : Renaming gen Δ Γ) → ∀ m → idx (lookupP (wkRen gen γ) m) ≡ suc (idx (lookupP γ m))
  wkRen-lem (y ∷ γ) m = {!!}

  lookup-lem : ∀ Δ m → idx (lookupP (idRen (Unit , (λ _ _ _ _ z _ _ → z)) Δ) m) ≡ m
  lookup-lem (tt ∷ Δ) zero = refl
  lookup-lem (tt ∷ Δ) (suc m) = {!!} ∙ cong suc (lookup-lem Δ m)
F .fst .F-seq = {!!}
F .snd = {!!}

-- reindexSCwFⱽSET : SCwFⱽ free-scwf-on-one-gen _ _ _ _
-- reindexSCwFⱽSET =
--   reindexSCwFⱽ {C = free-scwf-on-one-gen} {D = SCwFSET ℓ-zero}
--     F (SETⱽ _ ℓ-zero)

-- -- -- TODO elimLocal for SCwFᴰ
-- -- canonicalize :
-- --   StrictSection
-- --     free-scwf-on-one-gen
-- --     (SCwFⱽ→SCwFᴰ {Cᴰ = reindexSCwFⱽSET})
-- -- canonicalize =
-- --   elimSCwF gen
-- --     (SCwFⱽ→SCwFᴰ {Cᴰ = reindexSCwFⱽSET})
-- --     λ _ _ → Unit , isSetUnit

-- -- canonicity : ∀ {c} → (e : C [ 𝟙 , c ]) → CanonicalForm e
-- -- canonicity e = {!canonicalize .fst .F-homᴰ e !}
