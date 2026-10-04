{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
open import Cubical.Categories.Monoidal.Base hiding (MonoidalStr)
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Base renaming (Enrichment to VE)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Enriched.Enrichment.Functor.Base
open import Cubical.Categories.Enriched.Enrichment.BaseChange.Base

module Cubical.Categories.Direct.LocallyContractiveFiltered
  {ℓ ℓ' ℓC ℓC' ℓD ℓD' ℓO : Level}
  {A : Category ℓ ℓ'}
  {Wo : WFOrder ℓO ℓ'}
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  (ℰC : VE C (PshMon.𝓟Mon A ℓ))
  (ℰD : VE D (PshMon.𝓟Mon A ℓ))
  (dir : DirectStr A Wo)
  (F : Functor C D)
  (FE : Enrichment (PshMon.𝓟Mon A ℓ) ℰC ℰD F)
  where

open import Cubical.Categories.Direct.StrictDownset dir
open import Cubical.Categories.Monoidal.Functor.Instances.Presheaf.Later dir
  using (▷-strong; ▷-preservesUnderlying)
open import Cubical.Categories.Monoidal.NaturalTransformation.Base
  using (MonoidalNatTrans)
open import Cubical.Categories.Monoidal.NaturalTransformation.Instances.Presheaf.Next dir
  using (Id-lax; ▷-lax; nextNT-monoidal)
open import Cubical.Categories.NaturalTransformation using (NatTrans)
open import Cubical.Categories.Reasoning.Core

open DirectNotation dir using (_≺_)

private module A = Category A

-- The DirectStr hypotheses needed to make `▷` preserve the underlying
-- category — passed through to `▷-preservesUnderlying`.
module _
  (succ : ∀ (x : A.ob) → Σ[ y ∈ A.ob ] Σ[ g ∈ A [ x , y ] ] (x ≺ y))
  (join : ∀ (y : A.ob) (c₁ c₂ : A.ob) (g₁ : A [ y , c₁ ]) (g₂ : A [ y , c₂ ])
        → Σ[ c₃ ∈ A.ob ] Σ[ h₁ ∈ A [ c₁ , c₃ ] ] Σ[ h₂ ∈ A [ c₂ , c₃ ] ]
            ((g₁ A.⋆ h₁) ≡ (g₂ A.⋆ h₂)))
  where
  private
    V = PshMon.𝓟Mon A ℓ

    -- Id trivially preserves the underlying category: `ε̂ f = M.id ⋆ f = f`.
    pres-Id : LaxMonoidalFunctor.preservesUnderlyingCategories Id-lax
    pres-Id P = (λ f → f) , (λ _ → refl) , (λ _ → refl)

    -- ▷ preserves the underlying category, from the succ + join hypotheses.
    pres-▷ : LaxMonoidalFunctor.preservesUnderlyingCategories ▷-lax
    pres-▷ = ▷-preservesUnderlying succ join

    -- The ▷-base-change of ℰC.
    ▷*ℰC : VE C V
    ▷*ℰC = BaseChange ▷-lax pres-▷ ℰC

    -- next as an enriched functor: from ℰC to ▷*ℰC, underlying Id.
    -- The proofs mirror Prop 4.3.1's α*ℰC applied to `nextNT-monoidal`,
    -- inlined so the source enrichment is `ℰC` directly (α*ℰC's source
    -- is `BaseChange Id-lax pres-Id ℰC`, which is only propositionally
    -- equal to ℰC).
    module ℰC' = VE ℰC
    module nextNT' = MonoidalNatTrans nextNT-monoidal
    open Reasoning (MonoidalCategory.C V)
    private
      _ : Enrichment V
           (BaseChange Id-lax pres-Id ℰC)
           ▷*ℰC Id
      _ = α*ℰC nextNT-monoidal pres-Id pres-▷ ℰC

    next-Enr : Enrichment V ℰC ▷*ℰC Id
    next-Enr .Enrichment.F[_,_] x y = nextNT'.φ .NatTrans.N-ob ℰC'.VE[ x , y ]
    next-Enr .Enrichment.F-id {X} =
      glueTriL (nextNT'.φ .NatTrans.N-hom ℰC'.id) nextNT'.ε-law
    next-Enr .Enrichment.F-seq {X}{Y}{Z} =
      glue (nextNT'.μ-law ℰC'.VE[ X , Y ] ℰC'.VE[ Y , Z ])
           (sym (nextNT'.φ .NatTrans.N-hom (ℰC'.seq X Y Z)))
    next-Enr .Enrichment.agree f =
      sym (glueTriL (nextNT'.φ .NatTrans.N-hom ℰC'.⌜ f ⌝) nextNT'.ε-law)

  -- Def 7.2 (Birkedal et al 2012): F is locally contractive if it factors as an
  -- enriched composition  𝔻 ─next→ ▷𝔻 → ℂ.
  --
  -- Concretely: there exists an enriched functor G from ▷*(ℰC) to ℰD along F
  -- whose strength composed with `next` (pointwise, at each hom-object)
  -- recovers FE's strength.  (We state pointwise strength equality rather
  -- than full `G ∘Enr next-Enr ≡ FE` because the composite's underlying
  -- functor is `F ∘F Id`, which is only propositionally equal to `F`.)
  private
    module FE = Enrichment FE
    module next-Enr = Enrichment next-Enr

  isLocallyContractive : Type _
  isLocallyContractive =
    Σ[ G ∈ Enrichment V ▷*ℰC ℰD F ]
      let module G = Enrichment G
      in ∀ x y → FE.F[ x , y ]
                 ≡ (next-Enr.F[ x , y ]) ⋆PshHomStrict (G.F[ x , y ])
    where open import Cubical.Categories.Presheaf.StrictHom.Base
