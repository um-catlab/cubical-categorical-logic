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
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Representable.More

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
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

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

  -- Make this a more general lemma about composing /Fⱽ and /Fᴰ ?
  reindexRepresentable-seq : ∀ {x y f}
    → (Idᴰ /Fⱽ yoRec (D [-, F-ob F y ]) (F-hom F f)) ∘F (π Dᴰ F /Fᴰ Functor→PshHet F x)
      ≡ (π Dᴰ F /Fᴰ Functor→PshHet F y) ∘F (Idᴰ /Fⱽ yoRec (C [-, y ]) f)
  reindexRepresentable-seq = Functor≡ (λ _ → ΣPathP (refl , (ΣPathP (refl , (sym $ F .F-seq _ _)))))
    (λ _ → ΣPathP (refl , ΣPathP (refl , isSet→SquareP (λ i j → D.isSetHom) _ _ _ _)))

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (F : Functor C D) where
  private
    module Dᴰ = Fibers Dᴰ
  reindexCartesianLift : ∀ {x y}(f : C [ x , y ])(Fyᴰ : Dᴰ.ob[ F ⟅ y ⟆ ])
    → CartesianLift Dᴰ (F ⟪ f ⟫) Fyᴰ
    → CartesianLift (reindex Dᴰ F) f Fyᴰ
  reindexCartesianLift {x}{y} f Fyᴰ F⟪f⟫*Fyᴰ = (F⟪f⟫*Fyᴰ .fst)
    , reindexRepresentableIsoⱽ Dᴰ F _ _
      -- reindPsh (reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, F⟪f⟫*Fyᴰ ]
      ⋆PshIsoⱽ reindPshIso (reindex-π-/ Dᴰ F x) (F⟪f⟫*Fyᴰ .snd)
      -- reindPsh (reindex-π-/ Dᴰ F x) $ reindPsh (Idᴰ /Fⱽ yoRec (D [-, F-ob F y ]) (F-hom F f)) $ Dᴰ [-][-, F⟪f⟫*Fyᴰ ]
      ⋆PshIsoⱽ (reindPsh∘F≅ (reindex-π-/ Dᴰ F x) (Idᴰ /Fⱽ yoRec (D [-, F-ob F y ]) (F-hom F f)) (Dᴰ [-][-, Fyᴰ ])
      -- reindPsh (Idᴰ /Fⱽ yoRec (D [-, F-ob F y ]) (F-hom F f) ∘F reindex-π-/ Dᴰ F x) $ Dᴰ [-][-, F⟪f⟫*Fyᴰ ]
      ⋆PshIsoⱽ reindNatIsoPsh (pathToNatIso (reindexRepresentable-seq Dᴰ F))
        (Dᴰ [-][-, Fyᴰ ])
      -- reindPsh (π Dᴰ F /Fᴰ Functor→PshHet F y) ∘F (Idᴰ /Fⱽ yoRec (C [-, y ]) f) $ Dᴰ [-][-, F⟪f⟫*Fyᴰ ]
      ⋆PshIsoⱽ invPshIso (reindPsh∘F≅ (Idᴰ /Fⱽ yoRec (C [-, y ]) f) (reindex-π-/ Dᴰ F y) (Dᴰ [-][-, Fyᴰ ])))
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
