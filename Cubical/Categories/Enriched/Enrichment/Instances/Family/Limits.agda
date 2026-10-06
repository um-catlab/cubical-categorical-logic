{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module Cubical.Categories.Enriched.Enrichment.Instances.Family.Limits
  {ℓ ℓ' : Level} (A : Category ℓ ℓ') (ℓS : Level) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex using (becomesUniversal)
open import Cubical.Categories.Limits.BinProduct.More using (preservesBinProdCones)
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.HomFunctor
open import Cubical.Categories.Enriched.Enrichment.Limits.BinProduct
open import Cubical.Categories.Enriched.Enrichment.Instances.Power
  using (Setᴬ ; Fam-Psh-Enrichment)
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Limits A ℓS
  using (𝟙-terminal)
import Cubical.Categories.Enriched.Enrichment.Functor.Base as FE

open Functor
open NatTrans
open PshHomStrict
open PshMon A ℓS using (𝓟Mon ; 𝓟 ; ℓm)

private
  module A = Category A
  Fam = Setᴬ A.ob ℓm
  module Fam = Category Fam

famEnrichment : Enrichment Fam 𝓟Mon
famEnrichment = Fam-Psh-Enrichment A ℓS

module _ (Γ : Fam.ob) where
  Γ×Fam- : Functor Fam Fam
  Γ×Fam- .F-ob Y x = (⟨ Γ x ⟩ × ⟨ Y x ⟩) , isSet× (Γ x .snd) (Y x .snd)
  Γ×Fam- .F-hom f x (γ , y) = γ , f x y
  Γ×Fam- .F-id = refl
  Γ×Fam- .F-seq f g = refl

  π₁Γ : NatTrans Γ×Fam- (Constant Fam Fam Γ)
  π₁Γ .N-ob X x = fst
  π₁Γ .N-hom f = refl

  π₂Γ : NatTrans Γ×Fam- Id
  π₂Γ .N-ob X x = snd
  π₂Γ .N-hom f = refl

  ×-univ : ∀ X W → becomesUniversal (preservesBinProdCones (Hom[_,-] famEnrichment W) Γ X)
                      (Γ×Fam- ⟅ X ⟆) (π₁Γ ⟦ X ⟧ , π₂Γ ⟦ X ⟧)
  ×-univ X W Z = isoToIsEquiv (iso _ pair
    (λ (a , b) → ΣPathP (makePshHomStrictPath refl , makePshHomStrictPath refl))
    (λ h → makePshHomStrictPath refl))
    where
    H = Hom[_,-] famEnrichment W
    pair : 𝓟 [ Z , H ⟅ Γ ⟆ ] × 𝓟 [ Z , H ⟅ X ⟆ ] → 𝓟 [ Z , H ⟅ Γ×Fam- ⟅ X ⟆ ⟆ ]
    pair (a , b) .N-ob c z y h w = a .N-ob c z y h w , b .N-ob c z y h w
    pair (a , b) .N-hom c' c k z z' eq i y h w =
      a .N-hom c' c k z z' eq i y h w , b .N-hom c' c k z z' eq i y h w

  ×Fam-Enr : FE.Enrichment 𝓟Mon famEnrichment famEnrichment Γ×Fam-
  ×Fam-Enr = ×-Enrichment famEnrichment 𝟙-terminal Γ Γ×Fam- π₁Γ π₂Γ ×-univ
