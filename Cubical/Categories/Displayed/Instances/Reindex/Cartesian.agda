{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Reindex.Cartesian where

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
import Cubical.Data.Equality.More as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory
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
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.BinProduct.More
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.ChosenReind
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.Instances.Reindex.Properties
open import Cubical.Categories.Displayed.Instances.Reindex.UniversalProperties
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Limits.CartesianV'

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
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
    reindexReflectsUMPⱽ Dᴰ F x UnitPshᴰ 𝟙ⱽ
    ◁PshIsoⱽ reindPsh-Unit (reindex-π-/ Dᴰ F x)
  TerminalsⱽReindex : Terminalsⱽ Dᴰ → Terminalsⱽ (reindex Dᴰ F)
  TerminalsⱽReindex 𝟙ⱽs x = reindexTerminalⱽ x (𝟙ⱽs (F ⟅ x ⟆))

  reindexBinProductⱽ : ∀ {x} (Fxᴰ Fyᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → BinProductⱽ Dᴰ Fxᴰ Fyᴰ
    → BinProductⱽ (reindex Dᴰ F) Fxᴰ Fyᴰ
  reindexBinProductⱽ {x} Fxᴰ Fyᴰ Fxᴰ∧Fyᴰ =
    reindexReflectsUMPⱽ Dᴰ F x ((Dᴰ [-][-, Fxᴰ ]) ×ⱽPsh (Dᴰ [-][-, Fyᴰ ])) Fxᴰ∧Fyᴰ
    ◁PshIsoⱽ (reindPsh× (reindex-π-/ Dᴰ F x) (Dᴰ [-][-, Fxᴰ ]) (Dᴰ [-][-, Fyᴰ ])
              ⋆PshIsoⱽ ×PshIso (invPshIso (reindexRepresentableIsoⱽ Dᴰ F x Fxᴰ))
                               (invPshIso (reindexRepresentableIsoⱽ Dᴰ F x Fyᴰ)))

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

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (F : Functor C D) where
  private
    module Dᴰ = Categoryᴰ Dᴰ
    module Dop = Fibers (Dᴰ ^opᴰ)


  reindexInitialⱽ : ∀ x
    → Terminalⱽ (Dᴰ ^opᴰ) (F ⟅ x ⟆)
    → Terminalⱽ ((reindex Dᴰ F) ^opᴰ) x
  reindexInitialⱽ x init =
    init' .fst ,
    pshiso
      (pshhom (λ c → init' .snd .trans .N-ob c) (λ _ _ _ _ → refl))
      (init' .snd .nIso)
    where
    init' = reindexTerminalⱽ {Dᴰ = Dᴰ ^opᴰ} (F ^opFStrict) x init

  reindexBinCoProductⱽ : ∀ {x} (Fxᴰ Fyᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → BinProductⱽ (Dᴰ ^opᴰ) Fxᴰ Fyᴰ
    → BinProductⱽ ((reindex Dᴰ F) ^opᴰ) Fxᴰ Fyᴰ
  reindexBinCoProductⱽ Fxᴰ Fyᴰ bcp =
    bcp' .fst ,
    pshiso
      (pshhom (λ c → bcp' .snd .trans .N-ob c)
        (λ c c' g p → bcp' .snd .trans .N-hom c c' g p))
      (bcp' .snd .nIso)
    where
    bcp' = reindexBinProductⱽ {Dᴰ = Dᴰ ^opᴰ} (F ^opFStrict) Fxᴰ Fyᴰ bcp

  reindexBinCoProductⱽ-σ₁ : ∀ {x}
    (Fxᴰ Fyᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    (bcp : BinProductⱽ (Dᴰ ^opᴰ) Fxᴰ Fyᴰ)
    → BinProductⱽNotation.π₁ ((reindex Dᴰ F) ^opᴰ)
        (reindexBinCoProductⱽ Fxᴰ Fyᴰ bcp)
      Dop.∫≡ BinProductⱽNotation.π₁ (Dᴰ ^opᴰ) bcp
  reindexBinCoProductⱽ-σ₁ {x} Fxᴰ Fyᴰ bcp =
    cong toσ₁
      (congN-obⱽ {Γᴰ = bcp .fst} (bcp .snd .trans)
        (Dop.reind-revealed-filler⁻ {p = Dop.idᴰ} (sym (F .F-id))))
    where
    toσ₁ : (Σ[ f ∈ D [ F ⟅ x ⟆ , F ⟅ x ⟆ ] ]
      (Dᴰ [ f ][ Fxᴰ , bcp .fst ]) × (Dᴰ [ f ][ Fyᴰ , bcp .fst ]))
      → Dop.Hom[ (F ⟅ x ⟆ , bcp .fst) , (F ⟅ x ⟆ , Fxᴰ) ]
    toσ₁ (f , a , b) = f , a

  reindexBinCoProductⱽ-σ₂ : ∀ {x}
    (Fxᴰ Fyᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    (bcp : BinProductⱽ (Dᴰ ^opᴰ) Fxᴰ Fyᴰ)
    → BinProductⱽNotation.π₂ ((reindex Dᴰ F) ^opᴰ)
        (reindexBinCoProductⱽ Fxᴰ Fyᴰ bcp)
      Dop.∫≡ BinProductⱽNotation.π₂ (Dᴰ ^opᴰ) bcp
  reindexBinCoProductⱽ-σ₂ {x} Fxᴰ Fyᴰ bcp =
    cong toσ₂
      (congN-obⱽ {Γᴰ = bcp .fst} (bcp .snd .trans)
        (Dop.reind-revealed-filler⁻ {p = Dop.idᴰ} (sym (F .F-id))))
    where
    toσ₂ : (Σ[ f ∈ D [ F ⟅ x ⟆ , F ⟅ x ⟆ ] ]
      (Dᴰ [ f ][ Fxᴰ , bcp .fst ]) × (Dᴰ [ f ][ Fyᴰ , bcp .fst ]))
      → Dop.Hom[ (F ⟅ x ⟆ , bcp .fst) , (F ⟅ x ⟆ , Fyᴰ) ]
    toσ₂ (f , a , b) = f , b

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D) ⦃ cr : ChosenReind Dᴰ ⦄
  where
  private
    module C = Category C
    module D = Category D
    module Dᴰ = ChosenReindNotation Dᴰ

  reindexTerminalⱽChosenReind : ∀ x → Terminalⱽ Dᴰ (F ⟅ x ⟆)
    → Terminalⱽ (reindexChosenReind Dᴰ F) x
  reindexTerminalⱽChosenReind x 𝟙ⱽ =
    reindexReflectsUMPⱽChosenReind Dᴰ F x UnitPshᴰ 𝟙ⱽ
    ◁PshIsoⱽ reindPsh-Unit (reindex-π-/ChosenReind Dᴰ F x)

  TerminalsⱽReindexChosenReind : Terminalsⱽ Dᴰ
    → Terminalsⱽ (reindexChosenReind Dᴰ F)
  TerminalsⱽReindexChosenReind 𝟙ⱽs x =
    reindexTerminalⱽChosenReind x (𝟙ⱽs (F ⟅ x ⟆))

  reindexBinProductⱽChosenReind : ∀ {x} (Fxᴰ Fyᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → BinProductⱽ Dᴰ Fxᴰ Fyᴰ
    → BinProductⱽ (reindexChosenReind Dᴰ F) Fxᴰ Fyᴰ
  reindexBinProductⱽChosenReind {x} Fxᴰ Fyᴰ Fxᴰ∧Fyᴰ =
    reindexReflectsUMPⱽChosenReind Dᴰ F x
      ((Dᴰ [-][-, Fxᴰ ]) ×ⱽPsh (Dᴰ [-][-, Fyᴰ ])) Fxᴰ∧Fyᴰ
    ◁PshIsoⱽ (reindPsh× (reindex-π-/ChosenReind Dᴰ F x)
        (Dᴰ [-][-, Fxᴰ ]) (Dᴰ [-][-, Fyᴰ ])
      ⋆PshIsoⱽ ×PshIso
        (invPshIso (reindexRepresentableIsoⱽChosenReind Dᴰ F x Fxᴰ))
        (invPshIso (reindexRepresentableIsoⱽChosenReind Dᴰ F x Fyᴰ)))

  BinProductsⱽReindexChosenReind : BinProductsⱽ Dᴰ
    → BinProductsⱽ (reindexChosenReind Dᴰ F)
  BinProductsⱽReindexChosenReind bpⱽs Fxᴰ Fyᴰ =
    reindexBinProductⱽChosenReind Fxᴰ Fyᴰ (bpⱽs Fxᴰ Fyᴰ)

  isLRⱽReindexChosenReind : ∀ {x} (Pᴰ : Presheafⱽ (F ⟅ x ⟆) Dᴰ ℓQᴰ)
    → LocallyRepresentableⱽ Pᴰ
    → LocallyRepresentableⱽ (reindPsh (reindex-π-/ChosenReind Dᴰ F x) Pᴰ)
  isLRⱽReindexChosenReind Pᴰ _×ⱽ_*Pᴰ Γᴰ f .fst = (Γᴰ ×ⱽ (F ⟪ f ⟫) *Pᴰ) .fst
  isLRⱽReindexChosenReind {x = x} Pᴰ _×ⱽ_*Pᴰ {Γ} Γᴰ f .snd =
    (reindexRepresentableIsoⱽChosenReind Dᴰ F Γ ((Γᴰ ×ⱽ (F ⟪ f ⟫) *Pᴰ) .fst)
    ⋆PshIsoⱽ reindPshIso (reindex-π-/ChosenReind Dᴰ F Γ) ((Γᴰ ×ⱽ F-hom F f *Pᴰ)
      .snd)
    ⋆PshIsoⱽ reindPsh× (reindex-π-/ChosenReind Dᴰ F Γ) (Dᴰ [-][-, Γᴰ ])
      (reindPshᴰNatTrans (yoRec (D [-, F-ob F x ]) (F-hom F f)) Pᴰ)
    ⋆PshIsoⱽ
      ×PshIso (invPshIsoⱽ (reindexRepresentableIsoⱽChosenReind Dᴰ F Γ Γᴰ))
        (reindPsh-square (reindex-π-/ChosenReind Dᴰ F Γ)
          (Idᴰ /Fⱽ yoRec (D [-, F-ob F x ]) (F-hom F f))
          (Idᴰ /Fⱽ yoRec (C [-, x ]) f) (reindex-π-/ChosenReind Dᴰ F x) Pᴰ
          (reindexRepresentable-seq (πChosenReind Dᴰ F))))

  isLRⱽObᴰReindexChosenReind : ∀ {x} (xᴰ : Dᴰ.ob[ F ⟅ x ⟆ ])
    → isLRⱽObᴰ Dᴰ xᴰ
    → isLRⱽObᴰ (reindexChosenReind Dᴰ F) xᴰ
  isLRⱽObᴰReindexChosenReind {x} xᴰ _×ⱽ_*xᴰ {Γ} Γᴰ f =
    (Γᴰ ×ⱽ (F ⟪ f ⟫) *xᴰ) .fst
    ,
    improvePshIso
    (isLRⱽReindexChosenReind (Dᴰ [-][-, xᴰ ]) _×ⱽ_*xᴰ Γᴰ f .snd
    ⋆PshIsoⱽ ×PshIso idPshIso
      (reindPshIso (Idᴰ /Fⱽ yoRec (C [-, x ]) f) $
       invPshIso $
       reindexRepresentableIsoⱽChosenReind Dᴰ F x xᴰ))
    ((λ (Δ , Δᴰ , γ) γᴰ → (γᴰ ×ⱽ*xᴰ.⋆π₁ⱽ)
      , Dᴰ.reind⟨ sym $ F .F-seq γ f ⟩ (γᴰ ×ⱽ*xᴰ.⋆π₂ⱽ)) ,
    funExt λ (Δ , Δᴰ , γ) → funExt λ fᴰ → ΣPathP (refl , Dᴰ.rectifyOut
      (sym (Dᴰ.F.reind-filler _) ∙ Dᴰ.⋆IdL _ ∙ sym (Dᴰ.reind-∫≡ _ _))))
    ((λ (Δ , Δᴰ , γ) (γᴰ , γfᴰ) →
      ×ⱽ*xᴰ.introᴰ γᴰ (Dᴰ.reind⟨ F .F-seq γ f ⟩ γfᴰ))
    , funExt λ (Δ , Δᴰ , γ) → funExt λ (γᴰ , γfᴰ) →
      Dᴰ.rectifyOut $ ×ⱽ*xᴰ.cong-introᴰ refl
        (sym (Dᴰ.F.reind-filler _) ∙ Dᴰ.⋆IdL _ ∙ sym (Dᴰ.reind-∫≡ _ _)))
    where
      module ×ⱽ*xᴰ = LRⱽPresheafᴰNotation Dᴰ (_ , _×ⱽ_*xᴰ)

  AllLRⱽReindexChosenReind : AllLRⱽ Dᴰ → AllLRⱽ (reindexChosenReind Dᴰ F)
  AllLRⱽReindexChosenReind allLRⱽ {x} xᴰ = isLRⱽObᴰReindexChosenReind xᴰ (allLRⱽ
    xᴰ)

  module _ {x} (Fxᴰ : LRⱽObᴰ Dᴰ (F ⟅ x ⟆)) where
    private
      Fxᴰᴿ : LRⱽObᴰ (reindexChosenReind Dᴰ F) x
      Fxᴰᴿ = Fxᴰ .fst , isLRⱽObᴰReindexChosenReind (Fxᴰ .fst) (Fxᴰ .snd)
      module ×ⱽ*Fxᴰ = LRⱽPresheafᴰNotation Dᴰ (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ)

    opaque
      unfolding hSetReasoning.reind
      reindex-×LRⱽObᴰ-commuteChosenReind-π :
        (c : Category.ob (reindexChosenReind Dᴰ F / (C [-, x ]))) →
        Eq.mixedHEq
          (Eq.ap
            (λ Fc×Q → ((Dᴰ / (D [-, F-ob F x ])) [ Fc×Q , reindex-π-/ChosenReind
              Dᴰ F x ⟅ c ⟆ ])
              × PresheafNotation.p[ Dᴰ [-][-, Fxᴰ .fst ] ] Fc×Q)
            Eq.refl)
          (reindex-π-/ChosenReind Dᴰ F x ⟪
            LocallyRepresentableⱽ→LocallyRepresentable (Fxᴰᴿ .snd) c
              .UniversalElement.element .fst ⟫
          , reindexRepresentableIsoⱽChosenReind Dᴰ F x (Fxᴰ .fst) .trans .N-ob
            (LocallyRepresentableⱽ→LocallyRepresentable (Fxᴰᴿ .snd) c
              .UniversalElement.vertex)
            (LocallyRepresentableⱽ→LocallyRepresentable (Fxᴰᴿ .snd) c
              .UniversalElement.element .snd))
          (LocallyRepresentableⱽ→LocallyRepresentable (Fxᴰ .snd)
            (reindex-π-/ChosenReind Dᴰ F x ⟅ c ⟆) .UniversalElement.element)
      reindex-×LRⱽObᴰ-commuteChosenReind-π = λ (Γ , Γᴰ , f) →
        ΣPathP ((Hom/≡ ×ⱽ*Fxᴰ.⟨ Dᴰ.reind-∫≡ _ _ ⟩⋆π₁ⱽ) ,
          (Dᴰ.rectifyOut $
            sym (Dᴰ.F.reind-filler _)
            ∙ Dᴰ.reind-∫≡ _ _
            ∙ ×ⱽ*Fxᴰ.⟨ Dᴰ.reind-∫≡ _ _ ⟩⋆π₂ⱽ
            ∙ Dᴰ.F.reind-filler _))

    private
      LHS-F RHS-F : Functor (reindexChosenReind Dᴰ F / (C [-, x ])) (Dᴰ / (D [-,
        F ⟅ x ⟆ ]))
      LHS-F = ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ) ∘F (reindex-π-/ChosenReind Dᴰ F) x
      RHS-F = reindex-π-/ChosenReind Dᴰ F x ∘F ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ
        (reindexChosenReind Dᴰ F) Fxᴰᴿ)

      commute-strict : NatIso LHS-F RHS-F
      commute-strict =
        strictPresLRⱽ→NatIso {Cᴰ = reindexChosenReind Dᴰ F} {Dᴰ = Dᴰ} {P = C [-,
          x ]}
          {Q = D [-, F-ob F x ]}
          (reindex-π-/ChosenReind Dᴰ F x) (LRⱽObᴰ→LRⱽ (reindexChosenReind Dᴰ F)
            Fxᴰᴿ) (LRⱽObᴰ→LRⱽ Dᴰ Fxᴰ)
          (reindexRepresentableIsoⱽChosenReind Dᴰ F x (Fxᴰ .fst) .trans)
          (λ _ → Eq.refl)
          reindex-×LRⱽObᴰ-commuteChosenReind-π

      id/ : ∀ c → (Dᴰ / (D [-, F ⟅ x ⟆ ])) [ LHS-F ⟅ c ⟆ , RHS-F ⟅ c ⟆ ]
      id/ c = Category.id (Dᴰ / (D [-, F ⟅ x ⟆ ]))

      id/⁻ : ∀ c → (Dᴰ / (D [-, F ⟅ x ⟆ ])) [ RHS-F ⟅ c ⟆ , LHS-F ⟅ c ⟆ ]
      id/⁻ c = Category.id (Dᴰ / (D [-, F ⟅ x ⟆ ]))

    opaque
      commute-strict⁻≡id : (λ c → commute-strict .nIso c .isIso.inv) ≡ id/⁻
      commute-strict⁻≡id = funExt lem
        where
        lem : ∀ c → commute-strict .nIso c .isIso.inv ≡ id/⁻ c
        lem c = Category.⋆IdR (Dᴰ / (D [-, F ⟅ x ⟆ ])) _
          ∙ UQ.intro⟨ reindex-×LRⱽObᴰ-commuteChosenReind-π c ⟩
          ∙ sym UQ.weak-η
          where
          module UQ = UniversalElementNotation
            (LocallyRepresentableⱽ→LocallyRepresentable (Fxᴰ .snd)
              (reindex-π-/ChosenReind Dᴰ F x ⟅ c ⟆))

      commute-strict≡id : commute-strict .trans .N-ob ≡ id/
      commute-strict≡id = funExt λ c →
        sym (Category.⋆IdL (Dᴰ / (D [-, F ⟅ x ⟆ ])) _)
        ∙ cong (λ g → (Dᴰ / (D [-, F ⟅ x ⟆ ])) .Category._⋆_ g
                 (commute-strict .trans .N-ob c))
            (funExt⁻ (sym commute-strict⁻≡id) c)
        ∙ commute-strict .nIso c .isIso.sec

    reindex-×LRⱽObᴰ-commuteChosenReind : NatIso LHS-F RHS-F
    reindex-×LRⱽObᴰ-commuteChosenReind = improveNatIso commute-strict
      (_ , commute-strict≡id) (_ , commute-strict⁻≡id)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : CartesianCategoryⱽ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  ⦃ cr : ChosenReind (CartesianCategoryⱽ.Cᴰ Dᴰ) ⦄
  where
  private
    module Dᴰ = CartesianCategoryⱽ Dᴰ

  CartesianCategoryⱽReindexChosenReind : CartesianCategoryⱽ C ℓDᴰ ℓDᴰ'
  CartesianCategoryⱽReindexChosenReind =
    cartesiancategoryⱽ
      (reindexChosenReind Dᴰ.Cᴰ F)
      (TerminalsⱽReindexChosenReind Dᴰ.Cᴰ F Dᴰ.termⱽ)
      (BinProductsⱽReindexChosenReind Dᴰ.Cᴰ F Dᴰ.bpⱽ)
      (isFibrationReindexChosenReind Dᴰ.Cᴰ F Dᴰ.cartesianLifts)
