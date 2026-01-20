
module Cubical.Categories.Displayed.Constructions.Reindex.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.More
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.NaturalTransformation.Reind
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.FunctorComprehension.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Cartesian
open import Cubical.Categories.Displayed.Constructions.Reindex.Fibration
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties

open import Cubical.Categories.Displayed.Constructions.Reindex.UniversalProperties
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.ClosedV
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' ℓP ℓPᴰ ℓQ ℓQᴰ : Level

open Category
open Functor
open Functorᴰ
open NatTrans
open NatIso
open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module DR = Reasoning D
    module Dᴰ = Fibers Dᴰ
    module F*Dᴰ = Fibers (reindex Dᴰ F)

  -- Note: this proof does not appear to generalize to the large definition of the exponential.
  reindexExponentialⱽ : ∀ {x} (Fxᴰ : LRⱽObᴰ Dᴰ (F ⟅ x ⟆)) (Fyᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → Exponentialⱽ Dᴰ Fxᴰ Fyᴰ
    → Exponentialⱽ (reindex Dᴰ F) (LRⱽObᴰReindex F Fxᴰ) Fyᴰ
  reindexExponentialⱽ {x} Fxᴰ Fyᴰ Fxᴰ⇒ⱽFyᴰ = Fxᴰ⇒ⱽFyᴰ .fst
    -- reindex Dᴰ F [-][-, Fxᴰ ⇒ⱽ Fyᴰ ]
    , reindexRepresentableIsoⱽ Dᴰ F x (Fxᴰ⇒ⱽFyᴰ .fst)
    -- reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, Fxᴰ ⇒ⱽ Fyᴰ ]
    ⋆PshIsoⱽ reindPshIso (reindex-π-/ Dᴰ F x) (Fxᴰ⇒ⱽFyᴰ .snd)
    -- reindPsh (reindex-π-/ Dᴰ F x) $ reindPsh (×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ)) $ Dᴰ [-][-, Fyᴰ ]
    ⋆PshIsoⱽ reindPsh-square (reindex-π-/ Dᴰ F x) (×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ)) (×LRⱽPshᴰ (LRⱽReindex F (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ))) (reindex-π-/ Dᴰ F x) (Dᴰ [-][-, Fyᴰ ]) (reindex-×LRⱽPshᴰ-commute F (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ))
    -- reindPsh ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (reindex Dᴰ F) (LRⱽReindex Fxᴰ)) $ reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, Fyᴰ ]
    ⋆PshIsoⱽ reindPshIso (×LRⱽPshᴰ (LRⱽReindex F (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ))) (invPshIso (reindexRepresentableIsoⱽ Dᴰ F x Fyᴰ))
    -- reindPsh ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (reindex Dᴰ F) (LRⱽReindex Fxᴰ)) $ reindex Dᴰ F [-][-, Fyᴰ ]
    ⋆PshIsoⱽ reindNatIsoPsh (×LRⱽPshᴰ-Iso (LRⱽReindex F (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ)) (LRⱽObᴰ→LRⱽ (reindex Dᴰ F) (LRⱽObᴰReindex F Fxᴰ)) (invPshIso (reindexRepresentableIsoⱽ Dᴰ F x (LRⱽObᴰReindex F Fxᴰ .fst)))) (reindex Dᴰ F [-][-, Fyᴰ ])
    -- reindPsh ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (reindex Dᴰ F) (LRⱽReindex Fxᴰ)) $ (reindex Dᴰ F [-][-, Fyᴰ ])

  ExponentialsⱽReindex :
    ∀ (allLRⱽ : AllLRⱽ Dᴰ)
    → Exponentialsⱽ Dᴰ allLRⱽ
    → Exponentialsⱽ (reindex Dᴰ F) (AllLRⱽReindex F allLRⱽ)
  ExponentialsⱽReindex allLRⱽ expsⱽ xᴰ yᴰ = reindexExponentialⱽ (xᴰ , allLRⱽ xᴰ) yᴰ (expsⱽ xᴰ yᴰ)
