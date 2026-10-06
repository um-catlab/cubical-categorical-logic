module Cubical.Categories.Enriched.Enrichment.Instances.FullSubcategory where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Instances.FullSubcategory
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Guarded using (GuardedModel)
import Cubical.Categories.Enriched.Enrichment.Functor.Base as FE
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive using (isLocallyContractive)

open Enrichment

module _ {ℓV ℓV' ℓC ℓC' ℓP : Level} {V : MonoidalCategory ℓV ℓV'} {C : Category ℓC ℓC'}
  (ℰ : Enrichment C V) (P : Category.ob C → Type ℓP) where
  private
    module ℰ = Enrichment ℰ

  FullSubcategoryEnrichment : Enrichment (FullSubcategory C P) V
  FullSubcategoryEnrichment .VE[_,_] (x , _) (y , _) = ℰ.VE[ x , y ]
  FullSubcategoryEnrichment .id = ℰ.id
  FullSubcategoryEnrichment .seq (x , _) (y , _) (z , _) = ℰ.seq x y z
  FullSubcategoryEnrichment .⇄-agree = ℰ.⇄-agree
  FullSubcategoryEnrichment .⋆IdL (x , _) (y , _) = ℰ.⋆IdL x y
  FullSubcategoryEnrichment .⋆IdR (x , _) (y , _) = ℰ.⋆IdR x y
  FullSubcategoryEnrichment .⋆Assoc (x , _) (y , _) (z , _) (w , _) = ℰ.⋆Assoc x y z w
  FullSubcategoryEnrichment .⌜id⌝ = ℰ.⌜id⌝
  FullSubcategoryEnrichment .⌜⋆⌝ = ℰ.⌜⋆⌝

module _ {ℓV ℓV' ℓC ℓC' ℓD ℓD' ℓQ : Level} {V : MonoidalCategory ℓV ℓV'}
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {ℰC : Enrichment C V} {ℰD : Enrichment D V} {Q : Category.ob D → Type ℓQ}
  {F : Functor C D} (q : ∀ c → Q (F .Functor.F-ob c)) where

  ToFullSubcategory-Enr : FE.Enrichment V ℰC ℰD F
    → FE.Enrichment V ℰC (FullSubcategoryEnrichment ℰD Q) (ToFullSubcategory C D Q F q)
  ToFullSubcategory-Enr F̃ .FE.Enrichment.F[_,_] = F̃ .FE.Enrichment.F[_,_]
  ToFullSubcategory-Enr F̃ .FE.Enrichment.F-id = F̃ .FE.Enrichment.F-id
  ToFullSubcategory-Enr F̃ .FE.Enrichment.F-seq = F̃ .FE.Enrichment.F-seq
  ToFullSubcategory-Enr F̃ .FE.Enrichment.agree = F̃ .FE.Enrichment.agree

  module _ (G : GuardedModel V) where
    ToFullSubcategory-LC : isLocallyContractive G ℰC ℰD F
      → isLocallyContractive G ℰC (FullSubcategoryEnrichment ℰD Q) (ToFullSubcategory C D Q F q)
    ToFullSubcategory-LC (F̂ , agree) .fst .FE.EnrichmentFor.f[_,_] = F̂ .FE.EnrichmentFor.f[_,_]
    ToFullSubcategory-LC (F̂ , agree) .fst .FE.EnrichmentFor.fid = F̂ .FE.EnrichmentFor.fid
    ToFullSubcategory-LC (F̂ , agree) .fst .FE.EnrichmentFor.f-seq = F̂ .FE.EnrichmentFor.f-seq
    ToFullSubcategory-LC (F̂ , agree) .snd = agree
