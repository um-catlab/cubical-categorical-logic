{- Functors of SCwFs. These come in variants depending on whether the extension is preserved. -}
module Cubical.Categories.WithFamilies.Simple.Functor where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Limits.Terminal.More

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Properties

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

open PshHom
open Functor
open Category

module _ (S : SCwF ℓC ℓC' ℓS ℓS')(T : SCwF ℓD ℓD' ℓT ℓT') where
  private
    module S = SCwFNotation S
    module T = SCwFNotation T

  -- A PreFunctor is not required to preserve the terminal ctx or comprehensions
  record PreFunctor :
    Type (ℓ-max (ℓ-max (ℓ-max ℓS ℓT) (ℓ-max ℓS' ℓT'))
         (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD'))) where
    field
      F : Functor S.C T.C
      F-Ty : S.Ty → T.Ty
      F-Tm : ∀ {A} → PshHet F (S.Tm A) (T.Tm (F-Ty A))

    preservesExtPshHet : ∀ Γ A →
      PshHet F
        ((S.C [-, Γ ]) ×Psh S.Tm A)
        ((T.C [-, F ⟅ Γ ⟆ ]) ×Psh T.Tm (F-Ty A))
    preservesExtPshHet Γ A .N-ob Δ (γ , M) = F ⟪ γ ⟫ , F-Tm .N-ob Δ M
    preservesExtPshHet Γ A .N-hom c c' f (γ , M) =
      ΣPathP (F .F-seq f γ , F-Tm .N-hom c c' f M)

  record SCwFFunctor :
    Type (ℓ-max (ℓ-max (ℓ-max ℓS ℓT) (ℓ-max ℓS' ℓT'))
         (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD'))) where
    field
      F : PreFunctor
    private
      module F = PreFunctor F
    field
      pres-𝟙 : preservesTerminal S.C T.C F.F
      pres-comprehension : ∀ {A : S.Ty} {Γ : S.C .ob} →
        preservesUniversalElement (F.preservesExtPshHet Γ A) (S.ext A Γ)
