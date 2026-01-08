{-
  This proof is very ugly/manual. There should be a cleaner representability-based proof.
-}

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialV->D where

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
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
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
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialVD.Helper

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
    LHS-F RHS-F : Functor (Cᴰ / (C [-, A⇒B .vertex ])) (Cᴰ / (C [-, B ]))
    LHS-F = ((Idᴰ /Fⱽ yoRec (C [-, B ]) A⇒B.app) ∘F ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ Cᴰ (_ , ×ⱽπ₂*Aᴰ)) ∘F wkA Cᴰ A _×A (λ Γ Γᴰ → cartesianLifts Γᴰ _ _) A⇒B.⇒ue.vertex)
    RHS-F = (×ᴰPᴰ (_ , _×A) (_ , ×ᴰAᴰ) ∘F (Idᴰ /Fⱽ yoRec (reindPsh (LRPsh→Functor (_ , _×A)) (C [-, B ])) A⇒B.app))

    opaque
      ⇒ⱽᴰ-square-nat : ((Δ , Δᴰ , f) (Γ , Γᴰ , g) : ((Cᴰ / (C [-, A⇒B .vertex ]))) .ob)
        → ((γ , γᴰ , γg≡f) : ((Cᴰ / (C [-, A⇒B .vertex ]))) [ (Δ , Δᴰ , f) , (Γ , Γᴰ , g) ])
        → ((Fstⱽ Cᴰ (Element (C [-, B ])) ∘Fⱽᴰ Unitᴰ.recᴰ (compSectionFunctor Snd LHS-F)) .F-homᴰ {f = (γ , γᴰ , γg≡f)} _ Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-to Aᴰ ×ᴰAᴰ A⇒B cartesianLifts ×ⱽπ₂*Aᴰ Γ Γᴰ g)
          Cᴰ.∫≡ (⇒ⱽᴰ-square-isoᴰ Aᴰ ×ᴰAᴰ A⇒B cartesianLifts ×ⱽπ₂*Aᴰ Δ Δᴰ f .fst Cᴰ.⋆ᴰ (Fstⱽ Cᴰ (Element (C [-, B ])) ∘Fⱽᴰ Unitᴰ.recᴰ (compSectionFunctor Snd RHS-F)) .F-homᴰ {f = (γ , γᴰ , γg≡f)} _) 
      ⇒ⱽᴰ-square-nat (Δ , Δᴰ , f) (Γ , Γᴰ , g) (γ , γᴰ , γg≡f) = 
        Cᴰ.⟨⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
              ∙ ×ᴰAᴰ.×-extensionalityᴰ
                (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ ×ᴰAᴰ.×β₁ᴰ {pᴰ = ×ⱽπ₂*Aᴰ.π₂ⱽ cartesianLifts.⋆πⱽ} ∙ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ _ ⟩
                ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ ×ⱽπ₂*Aᴰ.β₁ⱽ _ (Cᴰ.reind _ _) ∙ sym (Cᴰ.reind-filler _ _) ∙ sym (Cᴰ.reind-filler _ _) ⟩⋆⟨⟩
                ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ cartesianLifts.βᴰ' _ ∙ sym (Cᴰ.reind-filler _ _) ⟩
                ∙ ((sym $ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ ×ᴰAᴰ.×β₁ᴰ {pᴰ = ×ᴰAᴰ.π₂ᴰ} ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ ×ᴰAᴰ.×β₁ᴰ {pᴰ = (×ⱽπ₂*Aᴰ.π₂ⱽ cartesianLifts.⋆πⱽ) } ∙ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ _ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _)))
                (sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ ×ᴰAᴰ.×β₂ᴰ {fᴰ = ×ⱽπ₂*Aᴰ.π₁ⱽ cartesianLifts.⋆πⱽ} ∙ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ _ ⟩
                ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ∙ ×ⱽπ₂*Aᴰ.β₂ⱽ (Cᴰ.reind _ (Cᴰ.reind _ _)) _ ∙ sym (Cᴰ.reind-filler _ _) ∙ sym (Cᴰ.reind-filler _ _) ∙ sym (Cᴰ.reind-filler _ _) ∙ sym (Cᴰ.reind-filler _ _) ⟩⋆⟨⟩
                ∙ ((sym $
                  sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ ×ᴰAᴰ.×β₂ᴰ {fᴰ = ×ᴰAᴰ.π₁ᴰ Cᴰ.⋆ᴰ γᴰ} ⟩
                    ∙ Cᴰ.reind-filler _ _ ∙ ×ᴰAᴰ.×β₂ᴰ {fᴰ = _ cartesianLifts.⋆πⱽ}
                    ∙ cartesianLifts.⋆πⱽ≡⋆ᴰπⱽ _))
                )
              ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩


    ⇒ⱽᴰ-square :
      NatIso {C = Cᴰ / (C [-, A⇒B .vertex ])}
             {D = Cᴰ / (C [-, B ])}
             LHS-F RHS-F
    ⇒ⱽᴰ-square = /NatIso
      (record { trans = natTrans (λ x → C.id) λ f → C.⋆IdR _ ; nIso = λ _ → idCatIso .snd })
      (isosToNatIsoᴰ _ _ _
        (λ {(Γ , Γᴰ , f)} _ → ⇒ⱽᴰ-square-isoᴰ Aᴰ ×ᴰAᴰ A⇒B cartesianLifts ×ⱽπ₂*Aᴰ Γ Γᴰ f)
        λ {(Δ , Δᴰ , f) (Γ , Γᴰ , g) _ _ (γ , γᴰ , γg≡f)}  _ → ⇒ⱽᴰ-square-nat (Δ , Δᴰ , f) (Γ , Γᴰ , g) (γ , γᴰ , γg≡f)
            )
      λ (Γ , Γᴰ , f) → C.⋆IdL _
