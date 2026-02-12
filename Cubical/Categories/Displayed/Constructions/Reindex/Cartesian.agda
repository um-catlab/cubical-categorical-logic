{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Reindex.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
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
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Fibration
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.UniversalProperties
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Limits.CartesianV'

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
    module D = Category D
    module Dᴰ = Fibers Dᴰ using (ob[_]; reind; reind-filler; rectify; ≡out; cong-reind; ⋆IdL)

  reindexTerminalⱽ : ∀ x → Terminalⱽ Dᴰ (F ⟅ x ⟆) → Terminalⱽ (reindex Dᴰ F) x
  reindexTerminalⱽ x 𝟙ⱽ =
    -- reindex Dᴰ F [-][-, 𝟙ⱽ ]
    reindexReflectsUMPⱽ Dᴰ F x UnitPshᴰ 𝟙ⱽ
    -- reindPsh (reindex-π-/ Dᴰ F x) $ UnitPshᴰ
    ◁PshIsoⱽ reindPsh-Unit (reindex-π-/ Dᴰ F x)
    -- UnitPshᴰ
  TerminalsⱽReindex : Terminalsⱽ Dᴰ → Terminalsⱽ (reindex Dᴰ F)
  TerminalsⱽReindex 𝟙ⱽs x = reindexTerminalⱽ x (𝟙ⱽs (F ⟅ x ⟆))

  reindexBinProductⱽ : ∀ {x} (Fxᴰ Fyᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → BinProductⱽ Dᴰ Fxᴰ Fyᴰ
    → BinProductⱽ (reindex Dᴰ F) Fxᴰ Fyᴰ
  reindexBinProductⱽ {x} Fxᴰ Fyᴰ Fxᴰ∧Fyᴰ =
    reindexReflectsUMPⱽ Dᴰ F x ((Dᴰ [-][-, Fxᴰ ]) ×ⱽPsh (Dᴰ [-][-, Fyᴰ ]))
    -- reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, Fxᴰ ] × Dᴰ [-][-, Fyᴰ ]
    Fxᴰ∧Fyᴰ
    ◁PshIsoⱽ (reindPsh× (reindex-π-/ Dᴰ F x) (Dᴰ [-][-, Fxᴰ ]) (Dᴰ [-][-, Fyᴰ ])
    ⋆PshIsoⱽ ×PshIso (invPshIso (reindexRepresentableIsoⱽ Dᴰ F x Fxᴰ)) (invPshIso (reindexRepresentableIsoⱽ Dᴰ F x Fyᴰ)))
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
    (reindexRepresentableIsoⱽ Dᴰ F Γ ((Γᴰ ×ⱽ (F ⟪ f ⟫) *Pᴰ) .fst)
    ⋆PshIsoⱽ reindPshIso (reindex-π-/ Dᴰ F Γ) ((Γᴰ ×ⱽ F-hom F f *Pᴰ) .snd)
    ⋆PshIsoⱽ reindPsh× (reindex-π-/ Dᴰ F Γ) (Dᴰ [-][-, Γᴰ ]) (reindPshᴰNatTrans (yoRec (D [-, F-ob F x ]) (F-hom F f)) Pᴰ)
    ⋆PshIsoⱽ
      ×PshIso (invPshIsoⱽ (reindexRepresentableIsoⱽ Dᴰ F Γ Γᴰ))
              (reindPsh-square (reindex-π-/ Dᴰ F Γ) (Idᴰ /Fⱽ yoRec (D [-, F-ob F x ]) (F-hom F f)) (Idᴰ /Fⱽ yoRec (C [-, x ]) f) (reindex-π-/ Dᴰ F x) Pᴰ
                (reindexRepresentable-seq (π Dᴰ F))))

  LRⱽReindex : ∀ {x} → (Pᴰ : LRⱽPresheafᴰ (D [-, F ⟅ x ⟆ ]) Dᴰ ℓPᴰ)
    → LRⱽPresheafᴰ (C [-, x ]) (reindex Dᴰ F) ℓPᴰ
  LRⱽReindex (Pᴰ , _×ⱽ_*Pᴰ) = (reindPsh (reindex-π-/ Dᴰ F _) Pᴰ) , (isLRⱽReindex Pᴰ _×ⱽ_*Pᴰ)

  isLRⱽObᴰReindex : ∀ {x} (xᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → isLRⱽObᴰ Dᴰ xᴰ
    → isLRⱽObᴰ (reindex Dᴰ F) xᴰ
  isLRⱽObᴰReindex {x} xᴰ _×ⱽ_*xᴰ {Γ} Γᴰ f =
    (Γᴰ ×ⱽ (F ⟪ f ⟫) *xᴰ) .fst
    ,
    improvePshIso
    (isLRⱽReindex (Dᴰ [-][-, xᴰ ]) _×ⱽ_*xᴰ Γᴰ f .snd
    ⋆PshIsoⱽ ×PshIso idPshIso
      (reindPshIso (Idᴰ /Fⱽ yoRec (C [-, x ]) f) $
       invPshIso $
       reindexRepresentableIsoⱽ Dᴰ F x xᴰ))
    ((λ (Δ , Δᴰ , γ) γᴰ → (γᴰ ×ⱽ*xᴰ.⋆π₁ⱽ) -- making this explicit is negligible
      , Dᴰ.reind (sym $ F .F-seq γ f) (γᴰ ×ⱽ*xᴰ.⋆π₂ⱽ)) ,
    funExt λ (Δ , Δᴰ , γ) → funExt λ fᴰ → ΣPathP (refl , (Dᴰ.rectify $ Dᴰ.≡out -- removing the second `ΣPathP (refl , (Dᴰ.rectify $ Dᴰ.≡out` is a big speedup

      $ Dᴰ.cong-reind _ _ -- making the first two args to cong-reind implicit is a noticable but smaller speedup
                      (Dᴰ.⋆IdL _))))
    ((λ (Δ , Δᴰ , γ) (γᴰ , γfᴰ) →
      ×ⱽ*xᴰ.introᴰ γᴰ (Dᴰ.reind (F .F-seq γ f) γfᴰ)) , funExt λ (Δ , Δᴰ , γ) → funExt λ (γᴰ , γfᴰ) →
      Dᴰ.rectify $ Dᴰ.≡out $ ×ⱽ*xᴰ.cong-introᴰ refl (Dᴰ.cong-reind _ _ (Dᴰ.⋆IdL _)))
    where
      module ×ⱽ*xᴰ = LRⱽPresheafᴰNotation Dᴰ (_ , _×ⱽ_*xᴰ)

  LRⱽObᴰReindex : ∀ {x} → LRⱽObᴰ Dᴰ (F ⟅ x ⟆) → LRⱽObᴰ (reindex Dᴰ F) x
  LRⱽObᴰReindex {x} (Fxᴰ , _×ⱽ_*Fxᴰ) = Fxᴰ , isLRⱽObᴰReindex Fxᴰ _×ⱽ_*Fxᴰ

  AllLRⱽReindex : AllLRⱽ Dᴰ → AllLRⱽ (reindex Dᴰ F)
  AllLRⱽReindex allLRⱽ {x} xᴰ = LRⱽObᴰReindex (xᴰ , allLRⱽ xᴰ) .snd

  module _ {x} (Pᴰ : LRⱽPresheafᴰ (D [-, F ⟅ x ⟆ ]) Dᴰ ℓPᴰ) where
    private
      module ×ⱽ*Pᴰ = LRⱽPresheafᴰNotation Dᴰ Pᴰ using (⟨_⟩⋆π₁ⱽ; ⟨_⟩⋆π₂ⱽ)
      module Pᴰ = PresheafᴰNotation Dᴰ (D [-, F ⟅ _ ⟆ ]) (Pᴰ .fst) using (≡out; rectify; reind-filler; formal-reind-filler)

    opaque
      unfolding hSetReasoning.reind
      reindex-×LRⱽPshᴰ-commute
        : NatIso ((×LRⱽPshᴰ Pᴰ) ∘F reindex-π-/ Dᴰ F x)
                (reindex-π-/ Dᴰ F x ∘F ×LRⱽPshᴰ (LRⱽReindex Pᴰ))
      reindex-×LRⱽPshᴰ-commute =
        strictPresLRⱽ→NatIso {Cᴰ = reindex Dᴰ F}{Dᴰ = Dᴰ}{P = C [-, x ]}{Q = D [-, F-ob F x ]}
          (reindex-π-/ {C = C}{D = D} Dᴰ F x) (LRⱽReindex Pᴰ) Pᴰ idPshHom
          (λ _ → Eq.refl)
        (λ (Γ , Γᴰ , f ) →
          ΣPathP ((Hom/≡ ×ⱽ*Pᴰ.⟨ sym $ Dᴰ.reind-filler _ ⟩⋆π₁ⱽ)
          , (Pᴰ.rectify $ Pᴰ.≡out $
            sym (Pᴰ.reind-filler _)
            -- this formal reind filler took a long time without the explicit argument. Why?
            ∙ Pᴰ.formal-reind-filler (reindexRepresentable-seq (π Dᴰ F) .nIso (Γ , Pᴰ .snd Γᴰ (F-hom F f) .fst , id C) .isIso.inv .snd .snd) _
            ∙ ×ⱽ*Pᴰ.⟨ sym $ Dᴰ.reind-filler _ ⟩⋆π₂ⱽ
            ∙ Pᴰ.reind-filler _)))

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : CartesianCategoryⱽ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where
  private
    module Dᴰ = CartesianCategoryⱽ Dᴰ using (Cᴰ; termⱽ; bpⱽ; cartesianLifts)
  CartesianCategoryⱽReindex : CartesianCategoryⱽ C ℓDᴰ ℓDᴰ'
  CartesianCategoryⱽReindex =
    cartesiancategoryⱽ
      (reindex Dᴰ.Cᴰ F)
      (TerminalsⱽReindex F Dᴰ.termⱽ)
      (BinProductsⱽReindex F Dᴰ.bpⱽ)
      (isFibrationReindex Dᴰ.Cᴰ F Dᴰ.cartesianLifts)
