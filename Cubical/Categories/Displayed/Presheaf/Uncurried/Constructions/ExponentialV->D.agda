{-
    module _ Γ (Γᴰ : Cᴰ.ob[ Γ ]) (f : C [ Γ , A⇒B .vertex ]) where
  This proof is very ugly/manual. There should be a cleaner representability-based proof.
-}

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialV->D where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More
open import Cubical.Data.Unit
open import Cubical.Categories.Category.Base
import Cubical.Categories.Bifunctor as Bif
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Exponentials.Small

open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
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
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq
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
open Functorᴰ

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
      ⇒ⱽᴰ-square-to =
        Cᴰ.reind p (×ᴰAᴰ.introᴰ ((×ⱽπ₂*Aᴰ.π₁ⱽ cartesianLifts.⋆πⱽ) , (×ⱽπ₂*Aᴰ.π₂ⱽ cartesianLifts.⋆πⱽ)))
        where
        abstract
          p : -×A.×ue.universal -×A.×ue.vertex .equiv-proof
              (C.id C.⋆ -×A.×ue.element .fst ,
              (C.id C.⋆
                -×A.×ue.universal -×A.×ue.vertex .equiv-proof
                (-×A.×ue.element .fst C.⋆ f , -×A.×ue.element .snd) .fst .fst)
              C.⋆ -×A.×ue.element .snd)
              .fst .fst
              ≡ C.id
          p = -×A.,p≡ refl (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ -×A.×β₂ ⟩)

      ⇒ⱽᴰ-square-from : Cᴰ.Hom[ C.id ][ Γᴰ ×ᴰAᴰ.×ᴰPᴰ  , (-×A.π₁ {Γ} cartesianLifts.* Γᴰ) ×ⱽπ₂*Aᴰ.×ⱽ ((-×A.π₁ C.⋆ f) -×A.,p -×A.π₂) * ]
      ⇒ⱽᴰ-square-from =
        ×ⱽπ₂*Aᴰ.introᴰ
          (cartesianLifts.introᴰ (Cᴰ.reind p ×ᴰAᴰ.π₁ᴰ))
          (cartesianLifts.introᴰ (Cᴰ.reind q ×ᴰAᴰ.π₂ᴰ))
        where
        abstract
          p :  -×A.×ue.element {b = Γ} .fst ≡ C.id C.⋆ -×A.×ue.element .fst
          p = sym $ C.⋆IdL (-×A.×ue.element .fst)

          q : -×A.×ue.element .snd ≡
            (C.id C.⋆
              -×A.×ue.universal -×A.×ue.vertex .equiv-proof
              (-×A.×ue.element .fst C.⋆ f , -×A.×ue.element .snd) .fst .fst)
            C.⋆ -×A.×ue.element .snd
          q = sym $ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ -×A.×β₂

      opaque
        ⇒ⱽᴰ-square-sec : (⇒ⱽᴰ-square-from Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-to) Cᴰ.∫≡ Cᴰ.idᴰ
        ⇒ⱽᴰ-square-sec =
          Cᴰ.⟨⟩⋆⟨ sym (Cᴰ.reind-filler _) ⟩
          ∙ ×ᴰAᴰ.×-extensionalityᴰ
              (Cᴰ.⋆Assoc _ _ _
              ∙ Cᴰ.⟨⟩⋆⟨ ×ᴰAᴰ.×β₁ᴰ {pᴰ = ×ⱽπ₂*Aᴰ.π₂ⱽ cartesianLifts.⋆πⱽ}
                        ∙ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ _ ⟩
              ∙ sym (Cᴰ.⋆Assoc _ _ _)
              ∙ Cᴰ.⟨ ×ⱽπ₂*Aᴰ.β₁ⱽ _ (cartesianLifts.introᴰ _) ⟩⋆⟨⟩
              ∙ cartesianLifts.βᴰ' _ ∙ sym (Cᴰ.reind-filler _) ∙ sym (Cᴰ.⋆IdL _))

          -- something slow here...
              (sym (Cᴰ.reind-filler _)
              ∙ Cᴰ.⋆Assoc _ _ _
              ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _
                        ∙ ×ᴰAᴰ.×β₂ᴰ {fᴰ = ×ⱽπ₂*Aᴰ.π₁ⱽ cartesianLifts.⋆πⱽ}
                        ∙ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ _ ⟩
              ∙ sym (Cᴰ.⋆Assoc _ _ _)
              ∙ Cᴰ.⟨ Cᴰ.reind-filler _
                     ∙ ×ⱽπ₂*Aᴰ.β₂ⱽ (cartesianLifts.introᴰ _) _ ⟩⋆⟨⟩
              ∙ cartesianLifts.βᴰ' _
              ∙ sym (Cᴰ.reind-filler _) ∙ (sym $ Cᴰ.⋆IdL _) ∙ Cᴰ.reind-filler _)

        ⇒ⱽᴰ-square-ret : (⇒ⱽᴰ-square-to Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-from) Cᴰ.∫≡ Cᴰ.idᴰ
        ⇒ⱽᴰ-square-ret =
          Cᴰ.⟨ sym (Cᴰ.reind-filler _) ⟩⋆⟨⟩
          ∙ ×ⱽπ₂*Aᴰ.extensionalityᴰ
              (×ⱽπ₂*Aᴰ.⋆π₁ⱽ-natural _ _
              ∙ Cᴰ.⟨⟩⋆⟨ ×ⱽπ₂*Aᴰ.β₁ⱽ' _ (cartesianLifts.introᴰ _) ⟩
              ∙ cartesianLifts.extensionalityᴰ
                  (C.⋆IdR _
                  ∙ -×A.×ue.intro≡
                      (ΣPathP (refl ,
                               (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ -×A.×β₂ ⟩))))
                  (cartesianLifts.⋆πⱽ-natural
                  ∙ Cᴰ.⟨⟩⋆⟨ cartesianLifts.βᴰ _ ∙ (sym $ Cᴰ.reind-filler _) ⟩
                  ∙ ×ᴰAᴰ.×β₁ᴰ {pᴰ = ×ⱽπ₂*Aᴰ.π₂ⱽ cartesianLifts.⋆πⱽ } ))
              (×ⱽπ₂*Aᴰ.⋆π₂ⱽ-natural _ _
              ∙ sym (Cᴰ.reind-filler _) ∙ Cᴰ.⟨⟩⋆⟨ ×ⱽπ₂*Aᴰ.β₂ⱽ' _ _ ⟩
              ∙ cartesianLifts.extensionalityᴰ
                  ((sym $
                  (C.⋆IdL _
                  ∙ -×A.×ue.intro≡
                      (ΣPathP (sym
                        (C.⋆Assoc _ _ _
                        ∙ C.⟨ refl ⟩⋆⟨ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ -×A.×β₁ ⟩
                        ∙ sym (C.⋆Assoc _ _ _) ∙ C.⟨ -×A.×β₁ ∙ C.⋆IdL _ ⟩⋆⟨ refl ⟩) ,
                        (sym $ C.⋆Assoc _ _ _
                        ∙ C.⟨ refl ⟩⋆⟨ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ -×A.×β₂ ⟩
                        ∙ -×A.×β₂ ∙ C.⋆Assoc _ _ _ ∙ C.⋆IdL _ ∙ -×A.×β₂))))))
                  (cartesianLifts.⋆πⱽ-natural
                  ∙ Cᴰ.⟨⟩⋆⟨ cartesianLifts.βᴰ _ ∙ (sym $ Cᴰ.reind-filler _) ⟩
                  ∙ Cᴰ.reind-filler _ ∙ ×ᴰAᴰ.×β₂ᴰ {fᴰ = ×ⱽπ₂*Aᴰ.π₁ⱽ cartesianLifts.⋆πⱽ}))


      ⇒ⱽᴰ-square-isoᴰ :
        CatIsoᴰ Cᴰ idCatIso
          ((-×A.π₁ {Γ} cartesianLifts.* Γᴰ) ×ⱽπ₂*Aᴰ.×ⱽ ((-×A.π₁ C.⋆ f) -×A.,p -×A.π₂) *) (Γᴰ ×ᴰAᴰ.×ᴰPᴰ)
      ⇒ⱽᴰ-square-isoᴰ =
        ⇒ⱽᴰ-square-to ,
        isisoᴰ ⇒ⱽᴰ-square-from
              (Cᴰ.rectify $ Cᴰ.≡out $ ⇒ⱽᴰ-square-sec)
              (Cᴰ.rectify $ Cᴰ.≡out $ ⇒ⱽᴰ-square-ret)

    LHS-F RHS-F : Functor (Cᴰ / (C [-, A⇒B .vertex ])) (Cᴰ / (C [-, B ]))
    LHS-F = (Idᴰ /Fⱽ yoRec (C [-, B ]) A⇒B.app)
            ∘F ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ Cᴰ (_ , ×ⱽπ₂*Aᴰ)) -- 2 hcomps
            -- ∘F {!!}
            ∘F wkA Cᴰ A _×A (λ Γ Γᴰ → cartesianLifts Γᴰ _ _) A⇒B.⇒ue.vertex -- 12 hcomps
    RHS-F = (×ᴰPᴰ (_ , _×A) (_ , ×ᴰAᴰ)
            ∘F (Idᴰ /Fⱽ yoRec (reindPsh (LRPsh→Functor (_ , _×A)) (C [-, B ])) A⇒B.app))

    opaque
      ⇒ⱽᴰ-square-nat : ((Δ , Δᴰ , f) (Γ , Γᴰ , g) : ((Cᴰ / (C [-, A⇒B .vertex ]))) .ob)
        → ((γ , γᴰ , γg≡f) :
            ((Cᴰ / (C [-, A⇒B .vertex ]))) [ (Δ , Δᴰ , f) ,
                                             (Γ , Γᴰ , g) ])
        → ((Fstⱽ Cᴰ (Element (C [-, B ]))
             ∘Fⱽᴰ Unitᴰ.recᴰ (compSectionFunctor Snd LHS-F))
             .F-homᴰ {f = (γ , γᴰ , γg≡f)} _
           Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-to Γ Γᴰ g)
          Cᴰ.∫≡
          (⇒ⱽᴰ-square-isoᴰ Δ Δᴰ f .fst Cᴰ.⋆ᴰ
            (Fstⱽ Cᴰ (Element (C [-, B ]))
              ∘Fⱽᴰ Unitᴰ.recᴰ (compSectionFunctor Snd RHS-F))
              .F-homᴰ {f = (γ , γᴰ , γg≡f)} _)
      ⇒ⱽᴰ-square-nat (Δ , Δᴰ , f) (Γ , Γᴰ , g) (γ , γᴰ , γg≡f) =
        Cᴰ.⟨⟩⋆⟨ sym $ Cᴰ.reind-filler _ ⟩
        ∙ ×ᴰAᴰ.×-extensionalityᴰ
            (Cᴰ.⋆Assoc _ _ _
              ∙ Cᴰ.⟨⟩⋆⟨ ×ᴰAᴰ.×β₁ᴰ {pᴰ = ×ⱽπ₂*Aᴰ.π₂ⱽ cartesianLifts.⋆πⱽ} ∙ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ ×ⱽπ₂*Aᴰ.π₁ⱽ ⟩
              ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
              ∙ Cᴰ.⟨ ×ⱽπ₂*Aᴰ.β₁ⱽ _ _ ⟩⋆⟨⟩
              ∙ Cᴰ.⋆Assoc _ _ _
              ∙ Cᴰ.⟨⟩⋆⟨ cartesianLifts.βᴰ' _ ∙ (sym $ Cᴰ.reind-filler _) ⟩
              ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
              ∙ Cᴰ.⟨ (sym $ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ _) ∙ (sym $ ×ᴰAᴰ.×β₁ᴰ {pᴰ = ×ⱽπ₂*Aᴰ.π₂ⱽ cartesianLifts.⋆πⱽ}) ⟩⋆⟨⟩
              ∙ Cᴰ.⟨ Cᴰ.⟨ Cᴰ.reind-filler _ ⟩⋆⟨⟩ ⟩⋆⟨⟩
              ∙ Cᴰ.⋆Assoc _ _ _
              ∙ Cᴰ.⟨⟩⋆⟨ sym $ ×ᴰAᴰ.×β₁ᴰ {pᴰ = ×ᴰAᴰ.π₂ᴰ} ⟩
              ∙ (sym $ Cᴰ.⋆Assoc _ _ _))
            ((sym $ Cᴰ.reind-filler _)
              ∙ Cᴰ.⋆Assoc _ _ _
              ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _
                         ∙ ×ᴰAᴰ.×β₂ᴰ {fᴰ = ×ⱽπ₂*Aᴰ.π₁ⱽ cartesianLifts.⋆πⱽ} ∙ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ ×ⱽπ₂*Aᴰ.π₂ⱽ ⟩
              ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
              ∙ Cᴰ.⟨ Cᴰ.reind-filler _
                     ∙ ×ⱽπ₂*Aᴰ.β₂ⱽ _ _
                     ∙ (sym $ Cᴰ.reind-filler _)
                     ∙ (sym $ Cᴰ.reind-filler _)
                     ⟩⋆⟨⟩
              ∙ (sym $ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ _)
              ∙ (sym $ ×ᴰAᴰ.×β₂ᴰ)
              ∙ (sym $ Cᴰ.reind-filler _)
              ∙ Cᴰ.⟨ Cᴰ.reind-filler _ ⟩⋆⟨⟩
              ∙ Cᴰ.⟨⟩⋆⟨ (sym $ ×ᴰAᴰ.×β₂ᴰ {fᴰ = ×ᴰAᴰ.π₁ᴰ Cᴰ.⋆ᴰ γᴰ})
                         ∙ (sym $ Cᴰ.reind-filler _) ⟩
              ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
              ∙ Cᴰ.reind-filler _
            )

    ⇒ⱽᴰ-square :
      NatIso {C = Cᴰ / (C [-, A⇒B .vertex ])}
             {D = Cᴰ / (C [-, B ])}
             LHS-F RHS-F
    ⇒ⱽᴰ-square = /NatIso
      (record { trans = natTrans (λ x → C.id) λ f → C.⋆IdR _ ; nIso = λ _ → idCatIso .snd })
      (isosToNatIsoᴰ _ _ _
        (λ {(Γ , Γᴰ , f)} _ → ⇒ⱽᴰ-square-isoᴰ Γ Γᴰ f)
        λ {(Δ , Δᴰ , f) (Γ , Γᴰ , g) _ _ (γ , γᴰ , γg≡f)}  _ → ⇒ⱽᴰ-square-nat (Δ , Δᴰ , f) (Γ , Γᴰ , g) (γ , γᴰ , γg≡f)
            )
      λ (Γ , Γᴰ , f) → C.⋆IdL _
