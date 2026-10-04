{-# OPTIONS --lossy-unification #-}
-- Enrichment of a `next`-like ordinary functor using the trivial
-- `Underlying` enrichment of the ▷-base-change — avoiding the need
-- for ▷ to preserve underlying categories (and hence the
-- filtered-direct hypotheses `succ`, `join` required for `next-Enr`
-- in `Cubical.Categories.Direct.LocallyContractiveFiltered`).
--
-- The construction mirrors `next-Enr` as closely as possible: the
-- strength at (x, y) is `nextNT ⟦ ℰC[x, y] ⟧`; the F-id/F-seq proofs
-- of the Enrichment are the identical `glueTriL`/`glue` ones using
-- nextNT's naturality and ε-/μ-laws; and `agree` is `refl` because
-- the target has `⇄-agree = idIso`.

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation using (NatTrans)
open import Cubical.Categories.Monoidal.Base hiding (MonoidalStr)
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.NaturalTransformation.Base
  using (MonoidalNatTrans)
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Reasoning.Core

open import Cubical.Categories.Enriched.Enrichment.Base
  renaming (Enrichment to VE)
open import Cubical.Categories.Enriched.Enrichment.Functor.Base
import Cubical.Categories.Enriched.BaseChange.Base as EnrBC
open import Cubical.Categories.Enriched.Enrichment.Instances.Underlying

module Cubical.Categories.Enriched.Enrichment.Functor.Instances.Presheaf.Next
  {ℓ ℓ' ℓC ℓC' ℓO : Level}
  {A : Category ℓ ℓ'}
  {Wo : WFOrder ℓO ℓ'}
  {C : Category ℓC ℓC'}
  (ℰC : VE C (PshMon.𝓟Mon A ℓ))
  (dir : DirectStr A Wo)
  where

open import Cubical.Categories.Direct.StrictDownset dir
open import Cubical.Categories.Monoidal.Functor.Instances.Presheaf.Later dir
  using (▷-strong)
open import Cubical.Categories.Monoidal.NaturalTransformation.Instances.Presheaf.Next dir
  using (Id-lax; ▷-lax; nextNT-monoidal)

private
  V = PshMon.𝓟Mon A ℓ
  module V = MonoidalCategory V
  module ℰC = VE ℰC
  module C = Category C
  module nextNT = MonoidalNatTrans nextNT-monoidal

  -- shorthand for `nextNT ⟦ X ⟧`
  next⟦_⟧ : ∀ (X : V.ob) → V.C [ X , ▷ .Functor.F-ob X ]
  next⟦ X ⟧ = nextNT.φ .NatTrans.N-ob X

open Reasoning V.C

-- ▷ base-change of ℰC, viewed as an EnrichedCategory
▷*ℰC-asEC : EnrichedCategory V ℓC
▷*ℰC-asEC = EnrBC.BaseChange ▷-lax (toEnrichedCategory C V ℰC)

-- The underlying ordinary category of its Γ-base-change.
Γ*▷*ℰC-Cat : Category ℓC _
Γ*▷*ℰC-Cat = Γ*C-Cat ▷*ℰC-asEC

open Category

-- The trivial Underlying enrichment on it: ⇄-agree = idIso.
target-Enr : VE Γ*▷*ℰC-Cat V
target-Enr = Underlying ▷*ℰC-asEC

-- Key V-level coherence: `(next ⊗ next) ⋆ ▷*ℰC-asEC.seq ≡ ℰC.seq ⋆ next`.
-- The core μ-law + nextNT-naturality fact at the heart of both
-- `Fun.F-seq` and `Next-Enr.F-seq`.
private
  seq-coh : ∀ {X Y Z : C.ob} →
      (next⟦ ℰC.VE[ X , Y ] ⟧ V.⊗ₕ next⟦ ℰC.VE[ Y , Z ] ⟧) V.⋆
          EnrichedCategory.seq ▷*ℰC-asEC X Y Z
    ≡ ℰC.seq X Y Z V.⋆ next⟦ ℰC.VE[ X , Z ] ⟧
  seq-coh {X} {Y} {Z} =
    glue (nextNT.μ-law ℰC.VE[ X , Y ] ℰC.VE[ Y , Z ])
         (sym (nextNT.φ .NatTrans.N-hom (ℰC.seq X Y Z)))

-- The identity-on-objects ordinary functor whose action on morphisms
-- is `⌜_⌝` composed with `nextNT`.  F-id/F-seq follow from the two
-- ⇄-agree-coherences plus nextNT's naturality + ε-/μ-laws.
Fun : Functor C Γ*▷*ℰC-Cat
Fun .Functor.F-ob x = x
Fun .Functor.F-hom {x} {y} f = ℰC.⌜ f ⌝ V.⋆ next⟦ ℰC.VE[ x , y ] ⟧
Fun .Functor.F-id {X} =
    cong (V._⋆ next⟦ ℰC.VE[ X , X ] ⟧) ℰC.⌜id⌝
  ∙ glueTriL (nextNT.φ .NatTrans.N-hom ℰC.id) nextNT.ε-law
Fun .Functor.F-seq {X} {Y} {Z} f g =
    cong (V._⋆ next⟦ ℰC.VE[ X , Z ] ⟧) (ℰC.⌜⋆⌝ f g)
  ∙ V.⋆Assoc _ _ _
  ∙ cong (V.η⁻¹⟨ V.unit ⟩ V.⋆_)
      (  V.⋆Assoc _ _ _
      ∙ cong ((ℰC.⌜ f ⌝ V.⊗ₕ ℰC.⌜ g ⌝) V.⋆_) (sym seq-coh)
      ∙ sym (V.⋆Assoc _ _ _)
      ∙ cong (V._⋆ EnrichedCategory.seq ▷*ℰC-asEC X Y Z)
          (sym (V.─⊗─ .Functor.F-seq
                  (ℰC.⌜ f ⌝ , ℰC.⌜ g ⌝)
                  (next⟦ ℰC.VE[ X , Y ] ⟧ , next⟦ ℰC.VE[ Y , Z ] ⟧)))
      )
  ∙ sym (V.⋆Assoc _ _ _)

-- The main enrichment.
-- * `F[_,_]` is `nextNT` — the "identity-like" universal strength.
-- * `F-id`/`F-seq` are the same `glueTriL`/`glue` proofs as `next-Enr`.
-- * `agree` is `refl`: `target-Enr.⌜_⌝ = idIso.fun = λ x → x`.
Next-Enr : Enrichment V ℰC target-Enr Fun
Next-Enr .Enrichment.F[_,_] x y = next⟦ ℰC.VE[ x , y ] ⟧
Next-Enr .Enrichment.F-id {X} =
  glueTriL (nextNT.φ .NatTrans.N-hom ℰC.id) nextNT.ε-law
Next-Enr .Enrichment.F-seq {X} {Y} {Z} = seq-coh
Next-Enr .Enrichment.agree f = refl
