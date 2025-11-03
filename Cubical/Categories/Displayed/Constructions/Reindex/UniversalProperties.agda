{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Reindex.UniversalProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
-- open import Cubical.Categories.Displayed.Fibration.Base
-- open import Cubical.Categories.Displayed.Presheaf hiding (PshIsoⱽ')
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor
open NatTrans
open NatIso
open PshHom

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

  reindexRepresentableIsoⱽ' : ∀ (x : C.ob)(Fxᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → PshIsoⱽ' (reindex Dᴰ F [-][-, Fxᴰ ]') (reindPsh (reindex-π-/ x) (Dᴰ [-][-, Fxᴰ ]'))
  reindexRepresentableIsoⱽ' x Fxᴰ .PshIso.trans .N-ob = λ c z → z
  reindexRepresentableIsoⱽ' x Fxᴰ .PshIso.trans .N-hom _ _ _ _ = Dᴰ.rectify $ Dᴰ.≡out $
    sym (Dᴰ.reind-filler _ _) ∙ sym (Dᴰ.reind-filler _ _) ∙ Dᴰ.reind-filler _ _
  reindexRepresentableIsoⱽ' x Fxᴰ .PshIso.nIso (y , yᴰ , f) =
    (λ z → z) , (λ _ → refl) , (λ _ → refl)

  -- Make this a more general lemma about composing /Fⱽ and /Fᴰ ?
  reindexRepresentable-seq : ∀ {x y f}
    → (Idᴰ /Fⱽ yoRec (D [-, F-ob F y ]) (F-hom F f)) ∘F (π Dᴰ F /Fᴰ Functor→PshHet F x)
      ≡ (π Dᴰ F /Fᴰ Functor→PshHet F y) ∘F (Idᴰ /Fⱽ yoRec (C [-, y ]) f)
  reindexRepresentable-seq = Functor≡ (λ _ → ΣPathP (refl , (ΣPathP (refl , (sym $ F .F-seq _ _)))))
    (λ _ → ΣPathP (refl , ΣPathP (refl , isSet→SquareP (λ i j → D.isSetHom) _ _ _ _)))
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (F : Functor C D) where

  isFibration'Reindex : isFibration' Dᴰ → isFibration' (reindex Dᴰ F)
  isFibration'Reindex isFibDᴰ {y} Fyᴰ x f = (isFibDᴰ Fyᴰ (F ⟅ x ⟆) (F ⟪ f ⟫) .fst)
    , reindexRepresentableIsoⱽ' Dᴰ F _ _
      ⋆PshIsoⱽ' reindPshIso (reindex-π-/ Dᴰ F x) (isFibDᴰ Fyᴰ (F-ob F x) (F-hom F f) .snd)
      ⋆PshIsoⱽ' (reindPsh∘F≅ (reindex-π-/ Dᴰ F x) (Idᴰ /Fⱽ yoRec (D [-, F-ob F y ]) (F-hom F f)) (Dᴰ [-][-, Fyᴰ ]')
      ⋆PshIsoⱽ' reindNatIsoPsh (pathToNatIso (reindexRepresentable-seq Dᴰ F))
        (Dᴰ [-][-, Fyᴰ ]')
      ⋆PshIsoⱽ' invPshIso (reindPsh∘F≅ (Idᴰ /Fⱽ yoRec (C [-, y ]) f) (reindex-π-/ Dᴰ F y) (Dᴰ [-][-, Fyᴰ ]')))
      ⋆PshIsoⱽ' (reindPshIso (Idᴰ /Fⱽ yoRec (C [-, y ]) f) (invPshIsoⱽ' (reindexRepresentableIsoⱽ' Dᴰ F y Fyᴰ)))
