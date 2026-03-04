{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Reindex.UniversalProperties where

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
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.FunctorComprehension.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.BinProduct.More
open import Cubical.Categories.Displayed.Instances.Graph.Presheaf
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Properties
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Limits.CartesianV'
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

  reindex-π-/ : (x : C.ob)
    → Functor (reindex Dᴰ F / (C [-, x ])) (Dᴰ / (D [-, F ⟅ x ⟆ ]))
  reindex-π-/ x = π Dᴰ F /Fᴰ Functor→PshHet F x

  reindexRepresentableIsoⱽ : ∀ (x : C.ob)(Fxᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → PshIsoⱽ (reindex Dᴰ F [-][-, Fxᴰ ]) (reindPsh (reindex-π-/ x) (Dᴰ [-][-, Fxᴰ ]))
  reindexRepresentableIsoⱽ x Fxᴰ =
    FFFunctorᴰ→PshIsoᴰ (π Dᴰ F) Fxᴰ (π-FFᴰ Dᴰ F)

  module _ (x : C.ob) (Qᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ) (ueⱽ : Representableⱽ Dᴰ (F ⟅ x ⟆) Qᴰ) where
    reindexReflectsUMPⱽ : Representableⱽ (reindex Dᴰ F) x (reindPsh (reindex-π-/ x) Qᴰ)
    reindexReflectsUMPⱽ .fst = ueⱽ .fst
    reindexReflectsUMPⱽ .snd =
      reindexRepresentableIsoⱽ x (ueⱽ .fst)
      ⋆PshIso reindPshIso (reindex-π-/ x) (ueⱽ .snd)

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (P : Presheaf C ℓP) (Q : Presheaf D ℓQ)
  (F : Functor C D) (FP : PshHet F P Q)
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
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

    module _ (Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ) where
      reindex-reflects-UMPᴰ :
        UniversalElementᴰ Dᴰ Q Qᴰ (preservesUniversalElement→UniversalElement FP ue FP-pres-ue)
        → UniversalElementᴰ (reindex Dᴰ F) P (reindPsh (π Dᴰ F /Fᴰ FP) Qᴰ) ue
      reindex-reflects-UMPᴰ ueᴰ = Representableᴰ→UniversalElementᴰOverUE (reindex Dᴰ F) P (reindPsh (π Dᴰ F /Fᴰ FP) Qᴰ) ue
        (ueᴰ .fst
        , (FiberwisePshIsoᴰ→PshIsoᴰ $
          reindexRepresentableIsoⱽ Dᴰ F (ue .UniversalElement.vertex) (ueᴰ .fst)
          ⋆PshIso reindPshIso (reindex-π-/ Dᴰ F (ue .UniversalElement.vertex)) (PshIsoᴰ→FiberwisePshIsoᴰ (UniversalElementᴰ→PshIsoᴰ Dᴰ Q Qᴰ _ ueᴰ))
          ⋆PshIso reindPsh-square _ _ _ _ _ reflect-UMP-square
          ))

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (P : Presheaf C ℓP) (Q : Presheaf D ℓQ)
  (F : Functor C D)
  -- (FP : PshHet F P Q)
  (termC : Terminal' C)
  (F-1 : preservesUniversalElement {D = D} {F = F} {Q = UnitPsh}
           (pshhom (λ _ x → x) (λ _ _ _ _ → refl)) termC)
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Termᴰ : ∀ termD → Terminalᴰ Dᴰ termD)
  where
  private
    module C = Category C
    module D = Category D
    module Q = PresheafNotation Q
    module Dᴰ = Fibers Dᴰ
    module F = Functor F

  ReindexTerminalᴰ : Terminalᴰ (reindex Dᴰ F) termC
  ReindexTerminalᴰ =
    reindex-reflects-UMPᴰ UnitPsh UnitPsh F
    (pshhom (λ _ _ → _) (λ _ _ _ _ → refl))
    Dᴰ termC
    F-1 UnitPshᴰ
    (Termᴰ (preservesUniversalElement→UniversalElement
      (pshhom (λ _ _ → _) (λ _ _ _ _ → refl)) termC F-1))
