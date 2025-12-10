{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Reindex.Fibration where

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
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties hiding (isFibrationReindex)
open import Cubical.Categories.Displayed.Constructions.Reindex.UniversalProperties
open import Cubical.Categories.Displayed.HLevels
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
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

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where
  private
    module C = Category C
    module D = Category D
    module Dᴰ = Fibers Dᴰ
    module F = Functor F

  reindexCartesianLift : ∀ {x y}(f : C [ x , y ])(Fyᴰ : Dᴰ.ob[ F ⟅ y ⟆ ])
    → CartesianLift Dᴰ (F ⟪ f ⟫) Fyᴰ
    → CartesianLift (reindex Dᴰ F) f Fyᴰ
  reindexCartesianLift {x}{y} f Fyᴰ F⟪f⟫*Fyᴰ = (F⟪f⟫*Fyᴰ .fst)
    , reindexRepresentableIsoⱽ Dᴰ F _ _
      -- reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, F⟪f⟫*Fyᴰ ]
      ⋆PshIsoⱽ reindPshIso (reindex-π-/ Dᴰ F x) (F⟪f⟫*Fyᴰ .snd)
      -- reindPsh (reindex-π-/ Dᴰ F x) $ reindPsh (Idᴰ /Fⱽ yoRec (D [-, F-ob F y ]) (F-hom F f)) $ Dᴰ [-][-, F⟪f⟫*Fyᴰ ]
      ⋆PshIsoⱽ reindPsh-square (reindex-π-/ Dᴰ F x) (Idᴰ /Fⱽ yoRec (D [-, F-ob F y ]) (F-hom F f)) (Idᴰ /Fⱽ yoRec (C [-, y ]) f) (reindex-π-/ Dᴰ F y) (Dᴰ [-][-, Fyᴰ ]) (reindexRepresentable-seq (π Dᴰ F))
      -- reindPsh (Idᴰ /Fⱽ yoRec (C [-, y ]) f) $ reindPsh (π Dᴰ F /Fᴰ Functor→PshHet F y) $ Dᴰ [-][-, F⟪f⟫*Fyᴰ ]
      ⋆PshIsoⱽ (reindPshIso (Idᴰ /Fⱽ yoRec (C [-, y ]) f) (invPshIsoⱽ (reindexRepresentableIsoⱽ Dᴰ F y Fyᴰ)))
      -- reindPsh (Idᴰ /Fⱽ yoRec (C [-, y ]) f) $ reindex Dᴰ F [-][-, F⟪f⟫*Fyᴰ ]

  isFibrationReindex : isFibration Dᴰ → isFibration (reindex Dᴰ F)
  isFibrationReindex isFibDᴰ {y} Fyᴰ x f = reindexCartesianLift f Fyᴰ (isFibDᴰ Fyᴰ (F ⟅ x ⟆) (F ⟪ f ⟫))
