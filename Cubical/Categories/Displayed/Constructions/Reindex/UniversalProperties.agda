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
  reindexRepresentableIsoⱽ x Fxᴰ = FFFunctorᴰ→PshIsoᴰ (π Dᴰ F) Fxᴰ (π-FFᴰ Dᴰ F)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (F : Functor C D) where
  private
    module C = Category C
    module D = Category D
    module DR = Reasoning D
    module Dᴰ = Fibers Dᴰ
    module F*Dᴰ = Fibers (reindex Dᴰ F)

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

  reindexTerminalⱽ : ∀ x → Terminalⱽ Dᴰ (F ⟅ x ⟆) → Terminalⱽ (reindex Dᴰ F) x
  reindexTerminalⱽ x 𝟙ⱽ = (𝟙ⱽ .fst)
    -- reindex Dᴰ F [-][-, 𝟙ⱽ ]
    , (reindexRepresentableIsoⱽ Dᴰ F _ _
    -- reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, 𝟙ⱽ ]
    ⋆PshIsoⱽ reindPshIso (reindex-π-/ Dᴰ F x) (𝟙ⱽ .snd)
    -- reindPsh (reindex-π-/ Dᴰ F x) $ UnitPshᴰ
    ⋆PshIsoⱽ reindPsh-Unit (reindex-π-/ Dᴰ F x))
    -- UnitPshᴰ

  TerminalsⱽReindex : Terminalsⱽ Dᴰ → Terminalsⱽ (reindex Dᴰ F)
  TerminalsⱽReindex 𝟙ⱽs x = reindexTerminalⱽ x (𝟙ⱽs (F ⟅ x ⟆))

  reindexBinProductⱽ : ∀ {x} (Fxᴰ Fyᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → BinProductⱽ Dᴰ Fxᴰ Fyᴰ
    → BinProductⱽ (reindex Dᴰ F) Fxᴰ Fyᴰ
  reindexBinProductⱽ {x} Fxᴰ Fyᴰ Fxᴰ∧Fyᴰ = Fxᴰ∧Fyᴰ .fst
    -- reindex Dᴰ F [-][-, Fxᴰ ∧ Fyᴰ ]
    , reindexRepresentableIsoⱽ Dᴰ F x (Fxᴰ∧Fyᴰ .fst)
    -- reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, Fxᴰ ∧ Fyᴰ ]
    ⋆PshIsoⱽ reindPshIso (reindex-π-/ Dᴰ F x) (Fxᴰ∧Fyᴰ .snd)
    -- reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, Fxᴰ ] × Dᴰ [-][-, Fyᴰ ]
    ⋆PshIsoⱽ reindPsh× (reindex-π-/ Dᴰ F x) (Dᴰ [-][-, Fxᴰ ]) (Dᴰ [-][-, Fyᴰ ])
    -- (reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, Fxᴰ ]) × (reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, Fyᴰ ])
    ⋆PshIsoⱽ ×PshIso (invPshIso (reindexRepresentableIsoⱽ Dᴰ F x Fxᴰ)) (invPshIso (reindexRepresentableIsoⱽ Dᴰ F x Fyᴰ))
    -- (reindex Dᴰ F [-][-, Fxᴰ ]) × (reindex Dᴰ F [-][-, Fyᴰ ])

  BinProductsⱽReindex : BinProductsⱽ Dᴰ → BinProductsⱽ (reindex Dᴰ F)
  BinProductsⱽReindex bpⱽs Fxᴰ Fyᴰ = reindexBinProductⱽ Fxᴰ Fyᴰ (bpⱽs Fxᴰ Fyᴰ)

  module _ {x} (Fxᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])(Qᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ) where
    private
      module Qᴰ = PresheafᴰNotation Dᴰ (D [-, F ⟅ x ⟆ ]) Qᴰ
  isLRⱽReindex : ∀ {x} (Pᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓPᴰ)
    → LocallyRepresentableⱽ Pᴰ
    → LocallyRepresentableⱽ (reindPsh (reindex-π-/ Dᴰ F x) Pᴰ)
  isLRⱽReindex Pᴰ _×ⱽ_*Pᴰ Γᴰ f .fst = (Γᴰ ×ⱽ (F ⟪ f ⟫) *Pᴰ) .fst
  isLRⱽReindex {x = x} Pᴰ _×ⱽ_*Pᴰ {Γ} Γᴰ f .snd =
    reindexRepresentableIsoⱽ Dᴰ F Γ (isLRⱽReindex Pᴰ _×ⱽ_*Pᴰ Γᴰ f .fst)
    ⋆PshIsoⱽ reindPshIso (reindex-π-/ Dᴰ F Γ) ((Γᴰ ×ⱽ F-hom F f *Pᴰ) .snd)
    ⋆PshIsoⱽ reindPsh× (reindex-π-/ Dᴰ F Γ) (Dᴰ [-][-, Γᴰ ]) (reindPshᴰNatTrans (yoRec (D [-, F-ob F x ]) (F-hom F f)) Pᴰ)
    ⋆PshIsoⱽ
      ×PshIso (invPshIsoⱽ (reindexRepresentableIsoⱽ Dᴰ F Γ Γᴰ))
              (reindPsh-square (reindex-π-/ Dᴰ F Γ) (Idᴰ /Fⱽ yoRec (D [-, F-ob F x ]) (F-hom F f)) (Idᴰ /Fⱽ yoRec (C [-, x ]) f) (reindex-π-/ Dᴰ F x) Pᴰ (reindexRepresentable-seq (π Dᴰ F)))

  LRⱽReindex : ∀ {x} → (Pᴰ : LRⱽPresheafᴰ (D [-, F ⟅ x ⟆ ]) Dᴰ ℓPᴰ)
    → LRⱽPresheafᴰ (C [-, x ]) (reindex Dᴰ F) ℓPᴰ
  LRⱽReindex (Pᴰ , _×ⱽ_*Pᴰ) = (reindPsh (reindex-π-/ Dᴰ F _) Pᴰ) , (isLRⱽReindex Pᴰ _×ⱽ_*Pᴰ)

  LRⱽObᴰReindex : ∀ {x} → LRⱽObᴰ Dᴰ (F ⟅ x ⟆) → LRⱽObᴰ (reindex Dᴰ F) x
  LRⱽObᴰReindex {x} (Fxᴰ , _×ⱽ_*Fxᴰ) = Fxᴰ , λ {Γ} Γᴰ f →
    (Γᴰ ×ⱽ (F ⟪ f ⟫) *Fxᴰ) .fst
    , isLRⱽReindex (Dᴰ [-][-, Fxᴰ ]) _×ⱽ_*Fxᴰ Γᴰ f .snd
    ⋆PshIsoⱽ ×PshIso idPshIso
      (reindPshIso (Idᴰ /Fⱽ yoRec (C [-, x ]) f) (invPshIso $ reindexRepresentableIsoⱽ Dᴰ F x Fxᴰ))

  reindex-×LRⱽPshᴰ-commute : ∀ {x} (Pᴰ : LRⱽPresheafᴰ (D [-, F ⟅ x ⟆ ]) Dᴰ ℓPᴰ)
    → NatIso ((×LRⱽPshᴰ Pᴰ) ∘F reindex-π-/ Dᴰ F x)
             (reindex-π-/ Dᴰ F x ∘F ×LRⱽPshᴰ (LRⱽReindex Pᴰ))
  reindex-×LRⱽPshᴰ-commute {ℓPᴰ}{x} Pᴰ = presLR→NatIso (reindex-π-/ Dᴰ F _) _ _ idPshHom
    (λ (Γ , Γᴰ , f) → substUniversalElement (LocallyRepresentableⱽ→LocallyRepresentable (Pᴰ .snd) (F ⟅ Γ ⟆ , Γᴰ , F ⟪ f ⟫)) _
      (ΣPathP ((ΣPathP ((sym $ F .F-id) , (ΣPathPProp (λ _ → D.isSetHom _ _)
      (Dᴰ.rectify $ Dᴰ.≡out $ ×ⱽ*Pᴰ.⟨ (Dᴰ.reind-filler _ _) ⟩⋆π₁ⱽ))))
      , (Pᴰ.rectify $ Pᴰ.≡out $ sym (Pᴰ.reind-filler _) ∙ ×ⱽ*Pᴰ.⟨ Dᴰ.reind-filler _ _ ⟩⋆π₂ⱽ ∙ (sym $ Pᴰ.formal-reind-filler _ _) ∙ Pᴰ.reind-filler _))))
    where
      module ×ⱽ*Pᴰ = LRⱽPresheafᴰNotation Dᴰ Pᴰ
      module Pᴰ = PresheafᴰNotation Dᴰ (D [-, F ⟅ _ ⟆ ]) (Pᴰ .fst)
      presCone-isUniversal :
        ∀ ((Γ , Γᴰ , f) : (reindex Dᴰ F / (C [-, x ])) .ob)
        → isUniversal (Dᴰ / (D [-, F ⟅ x ⟆ ])) (((Dᴰ / (D [-, F ⟅ x ⟆ ])) [-, reindex-π-/ Dᴰ F x ⟅ (Γ , Γᴰ , f) ⟆ ]) ×Psh Pᴰ .fst)
          ((F ⟅ Γ ⟆) , ((Pᴰ .snd Γᴰ (F ⟪ f ⟫) .fst) , (F ⟪ f ⟫)))
          ((D.id , ×ⱽ*Pᴰ.π₁ⱽ , (λ i → D.⋆IdL (F-hom F f) i)) , Pᴰ.reind _ ×ⱽ*Pᴰ.π₂ⱽ)
      presCone-isUniversal (Γ , Γᴰ , f) =
        LocallyRepresentableⱽ→LocallyRepresentable (Pᴰ .snd) (F ⟅ Γ ⟆ , Γᴰ , F ⟪ f ⟫) .UniversalElement.universal

  -- Note: this proof does not appear to generalize to the large definition of the exponential.
  reindexExponentialⱽ : ∀ {x} (Fxᴰ : LRⱽObᴰ Dᴰ (F ⟅ x ⟆)) (Fyᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → Exponentialⱽ Dᴰ Fxᴰ Fyᴰ
    → Exponentialⱽ (reindex Dᴰ F) (LRⱽObᴰReindex Fxᴰ) Fyᴰ
  reindexExponentialⱽ {x} Fxᴰ Fyᴰ Fxᴰ⇒ⱽFyᴰ = Fxᴰ⇒ⱽFyᴰ .fst
    -- reindex Dᴰ F [-][-, Fxᴰ ⇒ⱽ Fyᴰ ]
    , reindexRepresentableIsoⱽ Dᴰ F x (Fxᴰ⇒ⱽFyᴰ .fst)
    -- reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, Fxᴰ ⇒ⱽ Fyᴰ ]
    ⋆PshIsoⱽ reindPshIso (reindex-π-/ Dᴰ F x) (Fxᴰ⇒ⱽFyᴰ .snd)
    -- reindPsh (reindex-π-/ Dᴰ F x) $ reindPsh (×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ)) $ Dᴰ [-][-, Fyᴰ ]
    ⋆PshIsoⱽ reindPsh-square (reindex-π-/ Dᴰ F x) (×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ)) (×LRⱽPshᴰ (LRⱽReindex (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ))) (reindex-π-/ Dᴰ F x) (Dᴰ [-][-, Fyᴰ ]) (reindex-×LRⱽPshᴰ-commute (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ))
    -- reindPsh ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (reindex Dᴰ F) (LRⱽReindex Fxᴰ)) $ reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, Fyᴰ ]
    ⋆PshIsoⱽ reindPshIso (×LRⱽPshᴰ (LRⱽReindex (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ))) (invPshIso (reindexRepresentableIsoⱽ Dᴰ F x Fyᴰ))
    -- reindPsh ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (reindex Dᴰ F) (LRⱽReindex Fxᴰ)) $ reindex Dᴰ F [-][-, Fyᴰ ]
    ⋆PshIsoⱽ reindNatIsoPsh (×LRⱽPshᴰ-Iso (LRⱽReindex (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ)) (LRⱽObᴰ→LRⱽ (reindex Dᴰ F) (LRⱽObᴰReindex Fxᴰ)) (invPshIso (reindexRepresentableIsoⱽ Dᴰ F x (LRⱽObᴰReindex Fxᴰ .fst)))) (reindex Dᴰ F [-][-, Fyᴰ ])
    -- reindPsh ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ (reindex Dᴰ F) (LRⱽReindex Fxᴰ)) $ (reindex Dᴰ F [-][-, Fyᴰ ])
module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : CartesianCategoryⱽ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where
  private
    module Dᴰ = CartesianCategoryⱽ Dᴰ
  CartesianCategoryⱽReindex : CartesianCategoryⱽ C ℓDᴰ ℓDᴰ'
  CartesianCategoryⱽReindex =
    cartesiancategoryⱽ
      (reindex Dᴰ.Cᴰ F)
      (TerminalsⱽReindex F Dᴰ.termⱽ)
      (BinProductsⱽReindex F Dᴰ.bpⱽ)
      (isFibrationReindex F Dᴰ.cartesianLifts)
