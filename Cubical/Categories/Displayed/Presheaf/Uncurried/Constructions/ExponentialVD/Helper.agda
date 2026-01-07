{-
  This proof is very ugly/manual. There should be a cleaner representability-based proof.
-}

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialVD.Helper where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Exponentials.Small

open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open NatTrans
open NatIso
open PshHom
open PshIso
open UniversalElement

-- Setup is we have objects Aᴰ over A, Bᴰ over B
--
-- we have
-- 1. A is LROb
-- 2. Aᴰ is LRⱽObᴰ
-- 3. Aᴰ is LRᴰObᴰ over (A is LROb)
-- 4. A ⇒ B

-- And we want to construct a NatIso between the following functors

--                      wk A                             -×ⱽ Aᴰ
-- Cᴰ / C [-, A ⇒ B ] --------> Cᴰ / C [-, (A ⇒ B) × A ] -------> Cᴰ / C [-, (A ⇒ B) × A ]
--   |                                                              |
--   | Cᴰ / yoRec app                                               | Cᴰ / yoRec app
--   |                                                              |
--   \/                                                             \/
-- Cᴰ / -×A* C [-, B ] -----------------------------------------> Cᴰ / C [-, B ]
--                                 -xᴰ Aᴰ

open UniversalElement
open Category
open isIsoᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ {(A , _×A) : LROb C}{B}
    (Aᴰ : Cᴰ.ob[ A ])
    (×ᴰAᴰ : isLRᴰObᴰ Cᴰ (A , _×A) Aᴰ)
    (A⇒B : Exponential C A B _×A)
    (cartesianLifts : isFibration Cᴰ)
    -- π₂ * Aᴰ
    (×ⱽπ₂*Aᴰ : isLRⱽObᴰ Cᴰ (cartesianLifts Aᴰ (((A⇒B .vertex) ×A) .vertex) (((A⇒B .vertex) ×A) .element .snd) .fst))
    where
    private
      module cartesianLifts = FibrationNotation Cᴰ cartesianLifts
      module -×A = BinProductsWithNotation _×A
      module A⇒B = ExponentialNotation _×A A⇒B
      module ×ᴰAᴰ = LRᴰPresheafᴰNotation (_ , _×A) Cᴰ _ (_ , ×ᴰAᴰ)
      module ×ⱽπ₂*Aᴰ = LRⱽPresheafᴰNotation Cᴰ (_ , ×ⱽπ₂*Aᴰ)

    module _ Γ (Γᴰ : Cᴰ.ob[ Γ ]) (f : C [ Γ , A⇒B .vertex ]) where
      ⇒ⱽᴰ-square-to : Cᴰ.Hom[ C.id ][ (-×A.π₁ {Γ} cartesianLifts.* Γᴰ) ×ⱽπ₂*Aᴰ.×ⱽ ((-×A.π₁ C.⋆ f) -×A.,p -×A.π₂) * , Γᴰ ×ᴰAᴰ.×ᴰPᴰ ]
      ⇒ⱽᴰ-square-to = Cᴰ.reind (-×A.,p≡ refl (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ -×A.×β₂ ⟩)) ((×ᴰAᴰ.introᴰ ((×ⱽπ₂*Aᴰ.π₁ⱽ cartesianLifts.⋆πⱽ) , (×ⱽπ₂*Aᴰ.π₂ⱽ cartesianLifts.⋆πⱽ))))
      ⇒ⱽᴰ-square-from : Cᴰ.Hom[ C.id ][ Γᴰ ×ᴰAᴰ.×ᴰPᴰ  , (-×A.π₁ {Γ} cartesianLifts.* Γᴰ) ×ⱽπ₂*Aᴰ.×ⱽ ((-×A.π₁ C.⋆ f) -×A.,p -×A.π₂) * ]
      ⇒ⱽᴰ-square-from = ×ⱽπ₂*Aᴰ.introᴰ (cartesianLifts.introᴰ (Cᴰ.reind (sym $ C.⋆IdL _) ×ᴰAᴰ.π₁ᴰ)) (cartesianLifts.introᴰ (Cᴰ.reind (sym $ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ -×A.×β₂) ×ᴰAᴰ.π₂ᴰ))
      opaque
        ⇒ⱽᴰ-square-sec : (⇒ⱽᴰ-square-from Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-to) Cᴰ.∫≡ Cᴰ.idᴰ
        ⇒ⱽᴰ-square-sec = Cᴰ.⟨⟩⋆⟨ sym (Cᴰ.reind-filler _ _) ⟩ ∙ ×ᴰAᴰ.×-extensionalityᴰ
          (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ ×ᴰAᴰ.×β₁ᴰ {pᴰ = ×ⱽπ₂*Aᴰ.π₂ⱽ cartesianLifts.⋆πⱽ} ∙ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ _ ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ ×ⱽπ₂*Aᴰ.β₁ⱽ _ (cartesianLifts.introᴰ _) ⟩⋆⟨⟩ ∙ cartesianLifts.βᴰ' _ ∙ sym (Cᴰ.reind-filler _ _) ∙ sym (Cᴰ.⋆IdL _))
          -- something slow here...
          (sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ ×ᴰAᴰ.×β₂ᴰ {fᴰ = ×ⱽπ₂*Aᴰ.π₁ⱽ cartesianLifts.⋆πⱽ} ∙ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ _ ⟩
          ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ∙ ×ⱽπ₂*Aᴰ.β₂ⱽ (cartesianLifts.introᴰ _) _ ⟩⋆⟨⟩ ∙ (cartesianLifts.βᴰ' _ ∙ sym (Cᴰ.reind-filler _ _) ∙ (sym $ Cᴰ.⋆IdL _) ∙ Cᴰ.reind-filler _ _))

        ⇒ⱽᴰ-square-ret : (⇒ⱽᴰ-square-to Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-from) Cᴰ.∫≡ Cᴰ.idᴰ
        ⇒ⱽᴰ-square-ret = Cᴰ.⟨ sym (Cᴰ.reind-filler _ _) ⟩⋆⟨⟩ ∙ ×ⱽπ₂*Aᴰ.extensionalityᴰ
          (×ⱽπ₂*Aᴰ.⋆π₁ⱽ-natural _ _ ∙ Cᴰ.⟨⟩⋆⟨ ×ⱽπ₂*Aᴰ.β₁ⱽ' _ (cartesianLifts.introᴰ _) ⟩
            ∙ cartesianLifts.extensionalityᴰ (C.⋆IdR _ ∙ -×A.×ue.intro≡ (ΣPathP (refl , (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ -×A.×β₂ ⟩))))
                (cartesianLifts.⋆πⱽ-natural ∙ Cᴰ.⟨⟩⋆⟨ cartesianLifts.βᴰ _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩ ∙ ×ᴰAᴰ.×β₁ᴰ {pᴰ = ×ⱽπ₂*Aᴰ.π₂ⱽ cartesianLifts.⋆πⱽ } ))
          (×ⱽπ₂*Aᴰ.⋆π₂ⱽ-natural _ _ ∙ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨⟩⋆⟨ ×ⱽπ₂*Aᴰ.β₂ⱽ' _ _ ⟩
            ∙ cartesianLifts.extensionalityᴰ
              ((sym $ (C.⋆IdL _ ∙ -×A.×ue.intro≡ (ΣPathP
                (sym (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ -×A.×β₁ ⟩ ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ -×A.×β₁ ∙ C.⋆IdL _ ⟩⋆⟨ refl ⟩)
                , (sym $ C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ -×A.×β₂ ⟩ ∙ -×A.×β₂ ∙ C.⋆Assoc _ _ _ ∙ C.⋆IdL _ ∙ -×A.×β₂))))))
              (cartesianLifts.⋆πⱽ-natural ∙ Cᴰ.⟨⟩⋆⟨ cartesianLifts.βᴰ _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩ ∙ Cᴰ.reind-filler _ _ ∙ ×ᴰAᴰ.×β₂ᴰ {fᴰ = ×ⱽπ₂*Aᴰ.π₁ⱽ cartesianLifts.⋆πⱽ}))


      ⇒ⱽᴰ-square-isoᴰ : CatIsoᴰ Cᴰ idCatIso ((-×A.π₁ {Γ} cartesianLifts.* Γᴰ) ×ⱽπ₂*Aᴰ.×ⱽ ((-×A.π₁ C.⋆ f) -×A.,p -×A.π₂) *) (Γᴰ ×ᴰAᴰ.×ᴰPᴰ)
      ⇒ⱽᴰ-square-isoᴰ = ⇒ⱽᴰ-square-to , isisoᴰ ⇒ⱽᴰ-square-from (Cᴰ.rectify $ Cᴰ.≡out $ ⇒ⱽᴰ-square-sec) (Cᴰ.rectify $ Cᴰ.≡out $ ⇒ⱽᴰ-square-ret)
