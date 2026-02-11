{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Reindex.UniversalProperties where

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
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.FunctorComprehension.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
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

  reindex-π-/ : (x : C.ob)
    → Functor (reindex Dᴰ F / (C [-, x ])) (Dᴰ / (D [-, F ⟅ x ⟆ ]))
  reindex-π-/ x = π Dᴰ F /Fᴰ Functor→PshHet F x

  reindexRepresentableIsoⱽ : ∀ (x : C.ob)(Fxᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → PshIsoⱽ (reindex Dᴰ F [-][-, Fxᴰ ]) (reindPsh (reindex-π-/ x) (Dᴰ [-][-, Fxᴰ ]))
  reindexRepresentableIsoⱽ x Fxᴰ =
    FFFunctorᴰ→PshIsoᴰ (π Dᴰ F) Fxᴰ (π-FFᴰ Dᴰ F)

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (P : Presheaf C ℓP) (Q : Presheaf D ℓQ)
  (F : Functor C D) (FP : PshHet F P Q)
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ)
  where
  private
    module C = Category C
    module D = Category D
    module Q = PresheafNotation Q
    module Dᴰ = Fibers Dᴰ
    module F = Functor F

  module _ (ue : UniversalElement C P) (FP-pres-ue : preservesUniversalElement FP ue) where
    private
      module ue = UniversalElementNotation ue
    -- will result in unnecessary compositions with id
    reflect-UMP-square : NatIso
      ((Idᴰ /Fⱽ yoRec Q (FP .N-ob ue.vertex ue.element)) ∘F reindex-π-/ Dᴰ F ue.vertex)
      ((π Dᴰ F /Fᴰ FP) ∘F (Idᴰ /Fⱽ yoRec P ue.element))
    reflect-UMP-square .trans .N-ob (x , Fxᴰ , f) .fst = D.id
    reflect-UMP-square .trans .N-ob (x , Fxᴰ , f) .snd .fst = Dᴰ.idᴰ
    reflect-UMP-square .trans .N-ob (x , Fxᴰ , f) .snd .snd = Q.⋆IdL _ ∙ FP .N-hom _ _ _ _
    reflect-UMP-square .trans .N-hom f = Hom/≡ (Dᴰ.⋆IdR _ ∙ sym (Dᴰ.⋆IdL _))
    reflect-UMP-square .nIso (x , Fxᴰ , f) .isIso.inv .fst = D.id
    reflect-UMP-square .nIso (x , Fxᴰ , f) .isIso.inv .snd .fst = Dᴰ.idᴰ
    reflect-UMP-square .nIso (x , Fxᴰ , f) .isIso.inv .snd .snd = Q.⋆IdL _ ∙ sym (FP .N-hom _ _ _ _)
    reflect-UMP-square .nIso (x , Fxᴰ , f) .isIso.sec = Hom/≡ (Dᴰ.⋆IdL _)
    reflect-UMP-square .nIso (x , Fxᴰ , f) .isIso.ret = Hom/≡ (Dᴰ.⋆IdL _)

    reindex-reflects-UMP :
      UniversalElementᴰ Dᴰ Q Qᴰ (preservesUniversalElement→UniversalElement FP ue FP-pres-ue)
      → UniversalElementᴰ (reindex Dᴰ F) P (reindPsh (π Dᴰ F /Fᴰ FP) Qᴰ) ue
    reindex-reflects-UMP ueᴰ = Representableᴰ→UniversalElementᴰOverUE (reindex Dᴰ F) P (reindPsh (π Dᴰ F /Fᴰ FP) Qᴰ) ue
      (ueᴰ .fst
      , (FiberwisePshIsoᴰ→PshIsoᴰ $
        -- reindex Dᴰ F [-][-, ueᴰ .fst ]
        reindexRepresentableIsoⱽ Dᴰ F (ue .UniversalElement.vertex) (ueᴰ .fst)
        -- reind (reindex-π-/ Dᴰ F ue.vertex) $ Dᴰ [-][-, ueᴰ .fst ]
        ⋆PshIso reindPshIso (reindex-π-/ Dᴰ F (ue .UniversalElement.vertex)) (PshIsoᴰ→FiberwisePshIsoᴰ (UniversalElementᴰ→PshIsoᴰ Dᴰ Q Qᴰ _ ueᴰ))
        -- reind (reindex-π-/ Dᴰ F ue.vertex) $ reindPsh (yoRec (FP $ ueᴰ .element)) Qᴰ
        ⋆PshIso reindPsh-square _ _ _ _ _ reflect-UMP-square
        -- reind (yoRec ue.element) $ reindPsh (π Dᴰ F /Fᴰ FP) Qᴰ
        ))
