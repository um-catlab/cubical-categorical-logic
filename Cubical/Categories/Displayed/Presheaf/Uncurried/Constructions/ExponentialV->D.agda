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

open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Instances.TotalCategory as TotalCat
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Exponential
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
open import Cubical.Categories.Displayed.Instances.BinProduct.More
open import Cubical.Categories.Displayed.Instances.Graph.Presheaf
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
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

module _
  {C : Category ℓC ℓC'} {A B} {×A : BinProductsWith C A} {A⇒B : Exponential C A B ×A}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Aᴰ} {×Aᴰ : BinProductsWithᴰ Cᴰ ×A Aᴰ} {Bᴰ}
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module ×A = BinProductsWithNotation ×A
  open UniversalElement
  module _
    (Aᴰ[π₂] : CartesianLift Cᴰ (×A.π₂ {b = A⇒B .vertex}) Aᴰ)
    (Aᴰ[π₂]-lrⱽ : isLRⱽObᴰ Cᴰ (Aᴰ[π₂] .fst))
    (Bᴰ[app] : CartesianLift Cᴰ (A⇒B .element) Bᴰ)
    (Aᴰ[π₂]⇒Bᴰ[app] : Exponentialⱽ Cᴰ ((Aᴰ[π₂] .fst) , Aᴰ[π₂]-lrⱽ) (Bᴰ[app] .fst))
    (π₁-Quadrable : ∀ Γ → Quadrable Cᴰ (×A.π₁ {b = Γ}))
    (∀⟨Aᴰ[π₂]⇒Bᴰ[app]⟩ : UniversalQuantifier Cᴰ A ×A π₁-Quadrable (Aᴰ[π₂]⇒Bᴰ[app] .fst))
    where

    private
      π₁* : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) → Cᴰ.ob[ Γ ×A.×a ]
      π₁* {Γ} Γᴰ = π₁-Quadrable Γ Γᴰ .fst
      module π₁* {Γ : C.ob} = QuadrableNotation Cᴰ (π₁-Quadrable Γ)
      module Aᴰ[π₂] = CartesianLiftNotation Cᴰ Aᴰ[π₂]

      module A⇒B = ExponentialNotation ×A A⇒B
      module ×ᴰAᴰ = LRᴰPresheafᴰNotation (_ , ×A) Cᴰ _ (_ , ×Aᴰ)
      module ×ⱽπ₂*Aᴰ = LRⱽPresheafᴰNotation Cᴰ (_ , Aᴰ[π₂]-lrⱽ)

    module _ Γ (Γᴰ : Cᴰ.ob[ Γ ]) (f : C [ Γ , A⇒B .vertex ]) where
      ⇒ⱽᴰ-square-to : Cᴰ.Hom[ C.id ][ π₁* Γᴰ ×ⱽπ₂*Aᴰ.×ⱽ ((×A.π₁ C.⋆ f) ×A.,p ×A.π₂) * , Γᴰ ×ᴰAᴰ.×ᴰPᴰ ]
      ⇒ⱽᴰ-square-to = Cᴰ.reind (×A.,p≡ refl (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ ×A.×β₂ ⟩))
        (×ᴰAᴰ.introᴰ ((×ⱽπ₂*Aᴰ.π₁ⱽ π₁*.⋆πⱽ) , (×ⱽπ₂*Aᴰ.π₂ⱽ Aᴰ[π₂].⋆πⱽ)))

      ⇒ⱽᴰ-square-from : Cᴰ.Hom[ C.id ][ Γᴰ ×ᴰAᴰ.×ᴰPᴰ  , (π₁* Γᴰ) ×ⱽπ₂*Aᴰ.×ⱽ ((×A.π₁ C.⋆ f) ×A.,p ×A.π₂) * ]
      ⇒ⱽᴰ-square-from = ×ⱽπ₂*Aᴰ.introᴰ
        (π₁*.introᴰ (Cᴰ.reind (sym $ C.⋆IdL _)
                              ×ᴰAᴰ.π₁ᴰ))
        (Aᴰ[π₂].introᴰ (Cᴰ.reind (sym $ C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ ×A.×β₂)
                                 ×ᴰAᴰ.π₂ᴰ))

      -- ⇒ⱽᴰ-square-to is Cᴰ.reind e (introᴰ …), so every use of it in a
      -- chain has to cross that reind. Its two β laws are stated here once,
      -- against ∫, so that the chains below do not restate the crossing.
      to-β₁ :
        Path Cᴰ.Hom[ _ , _ ]
          (_ , ⇒ⱽᴰ-square-to Cᴰ.⋆ᴰ ×ᴰAᴰ.π₁ᴰ)
          (_ , ×ⱽπ₂*Aᴰ.π₁ⱽ Cᴰ.⋆ᴰ π₁*.πⱽ)
      to-β₁ = Cᴰ.⟨ Cᴰ.reind-filler⁻ _ ⟩⋆⟨⟩ ∙ ×ᴰAᴰ.×β₁ᴰ ∙ π₁*.⋆πⱽ≡⋆ᴰπⱽ _

      to-β₂ :
        Path Cᴰ.Hom[ _ , _ ]
          (_ , ⇒ⱽᴰ-square-to Cᴰ.⋆ᴰ ×ᴰAᴰ.π₂ᴰ)
          (_ , ×ⱽπ₂*Aᴰ.π₂ⱽ Cᴰ.⋆ᴰ Aᴰ[π₂].πⱽ)
      to-β₂ = Cᴰ.⟨ Cᴰ.reind-filler⁻ _ ⟩⋆⟨⟩
        ∙ Cᴰ.reind-filler _ ∙ ×ᴰAᴰ.×β₂ᴰ ∙ Aᴰ[π₂].⋆πⱽ≡⋆ᴰπⱽ _

      -- The two legs of the naturality square, with the functor terms
      -- abstracted into a variable, so that each is proved once against
      -- variable endpoints rather than against elaborated F-homᴰ terms.
      ⋆to-β₁ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{h}
        (hᴰ : Cᴰ [ h ][ Δᴰ , (π₁* Γᴰ) ×ⱽπ₂*Aᴰ.×ⱽ ((×A.π₁ C.⋆ f) ×A.,p ×A.π₂) * ])
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , (hᴰ Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-to) Cᴰ.⋆ᴰ ×ᴰAᴰ.π₁ᴰ)
            (_ , (hᴰ Cᴰ.⋆ᴰ ×ⱽπ₂*Aᴰ.π₁ⱽ) Cᴰ.⋆ᴰ π₁*.πⱽ)
      ⋆to-β₁ hᴰ = Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ to-β₁ ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _)

      ⋆to-β₂ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{h}
        (hᴰ : Cᴰ [ h ][ Δᴰ , (π₁* Γᴰ) ×ⱽπ₂*Aᴰ.×ⱽ ((×A.π₁ C.⋆ f) ×A.,p ×A.π₂) * ])
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , (hᴰ Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-to) ×ᴰAᴰ.⋆ᴰ ×ᴰAᴰ.π₂ᴰ)
            (_ , (hᴰ Cᴰ.⋆ᴰ ×ⱽπ₂*Aᴰ.π₂ⱽ) Cᴰ.⋆ᴰ Aᴰ[π₂].πⱽ)
      ⋆to-β₂ hᴰ =
        Cᴰ.reind-filler⁻ _ ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ to-β₂ ⟩
        ∙ sym (Cᴰ.⋆Assoc _ _ _)

      -- The mirror-image legs, with ⇒ⱽᴰ-square-to on the left of the
      -- composite and the ×ᴰPᴰ functor's action introᴰ (π₁ᴰ ⋆ᴰ wᴰ , π₂ᴰ)
      -- on the right.
      to⋆-β₁ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{w}(wᴰ : Cᴰ [ w ][ Γᴰ , Δᴰ ])
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , (⇒ⱽᴰ-square-to Cᴰ.⋆ᴰ ×ᴰAᴰ.introᴰ ((×ᴰAᴰ.π₁ᴰ Cᴰ.⋆ᴰ wᴰ) , ×ᴰAᴰ.π₂ᴰ))
                   Cᴰ.⋆ᴰ ×ᴰAᴰ.π₁ᴰ)
            (_ , ×ⱽπ₂*Aᴰ.π₁ⱽ Cᴰ.⋆ᴰ (π₁*.πⱽ Cᴰ.⋆ᴰ wᴰ))
      to⋆-β₁ wᴰ = Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ ×ᴰAᴰ.×β₁ᴰ ⟩
        ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ to-β₁ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _

      to⋆-β₂ : ∀ {Δ}{Δᴰ : Cᴰ.ob[ Δ ]}{w}(wᴰ : Cᴰ [ w ][ Γᴰ , Δᴰ ])
        → Path Cᴰ.Hom[ _ , _ ]
            (_ , (⇒ⱽᴰ-square-to Cᴰ.⋆ᴰ ×ᴰAᴰ.introᴰ ((×ᴰAᴰ.π₁ᴰ Cᴰ.⋆ᴰ wᴰ) , ×ᴰAᴰ.π₂ᴰ))
                   ×ᴰAᴰ.⋆ᴰ ×ᴰAᴰ.π₂ᴰ)
            (_ , ×ⱽπ₂*Aᴰ.π₂ⱽ Cᴰ.⋆ᴰ Aᴰ[π₂].πⱽ)
      to⋆-β₂ wᴰ = Cᴰ.reind-filler⁻ _ ∙ Cᴰ.⋆Assoc _ _ _
        ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ ∙ ×ᴰAᴰ.×β₂ᴰ ⟩ ∙ to-β₂

      ⇒ⱽᴰ-square-sec : (⇒ⱽᴰ-square-from Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-to) Cᴰ.∫≡ Cᴰ.idᴰ
      ⇒ⱽᴰ-square-sec = ×ᴰAᴰ.×-extensionalityᴰ
        (⋆to-β₁ _ ∙ Cᴰ.⟨ ×ⱽπ₂*Aᴰ.β₁ⱽ _ _ ⟩⋆⟨⟩
        ∙ π₁*.βᴰ' _
        ∙ Cᴰ.reind-filler⁻ _ ∙ sym (Cᴰ.⋆IdL _))
        (⋆to-β₂ _ ∙ Cᴰ.⟨ Cᴰ.reind-filler _ ∙ ×ⱽπ₂*Aᴰ.β₂ⱽ _ _ ⟩⋆⟨⟩
        ∙ Aᴰ[π₂].βᴰ' _
        ∙ Cᴰ.reind-filler⁻ _ ∙ (sym $ Cᴰ.⋆IdL _) ∙ Cᴰ.reind-filler _)

      ⇒ⱽᴰ-square-ret : (⇒ⱽᴰ-square-to Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-from) Cᴰ.∫≡ Cᴰ.idᴰ
      ⇒ⱽᴰ-square-ret = Cᴰ.⟨ Cᴰ.reind-filler⁻ _ ⟩⋆⟨⟩ ∙ ×ⱽπ₂*Aᴰ.extensionalityᴰ
        (×ⱽπ₂*Aᴰ.⋆π₁ⱽ-natural _ _ ∙ Cᴰ.⟨⟩⋆⟨ ×ⱽπ₂*Aᴰ.β₁ⱽ' _ _ ⟩ ∙ π₁*.extensionalityᴰ
          (C.⋆IdR _ ∙ ×A.,p≡ refl (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ ×A.×β₂ ⟩)) -- is this the same as the goal in ⇒ⱽᴰ-square-to ?
          (π₁*.⋆πⱽ-natural ∙ Cᴰ.⟨⟩⋆⟨ π₁*.βᴰ _ ∙ Cᴰ.reind-filler⁻ _ ⟩ ∙ ×ᴰAᴰ.×β₁ᴰ))
        (×ⱽπ₂*Aᴰ.⋆π₂ⱽ-natural _ _ ∙ Cᴰ.reind-filler⁻ _ ∙ Cᴰ.⟨⟩⋆⟨ ×ⱽπ₂*Aᴰ.β₂ⱽ' _ _ ⟩ ∙ Aᴰ[π₂].extensionalityᴰ
          (C.⟨ ×A.,p≡ refl (C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ ×A.×β₂ ⟩) ⟩⋆⟨ refl ⟩ ∙ C.⋆IdL _)
          (Aᴰ[π₂].⋆πⱽ-natural ∙ Cᴰ.⟨⟩⋆⟨ Aᴰ[π₂].βᴰ _ ∙ Cᴰ.reind-filler⁻ _ ⟩
          ∙ Cᴰ.reind-filler _ ∙ ×ᴰAᴰ.×β₂ᴰ))

      ⇒ⱽᴰ-square-isoᴰ : CatIsoᴰ Cᴰ idCatIso ((π₁* Γᴰ) ×ⱽπ₂*Aᴰ.×ⱽ ((×A.π₁ C.⋆ f) ×A.,p ×A.π₂) *) (Γᴰ ×ᴰAᴰ.×ᴰPᴰ)
      ⇒ⱽᴰ-square-isoᴰ .fst = ⇒ⱽᴰ-square-to
      ⇒ⱽᴰ-square-isoᴰ .snd .invᴰ = ⇒ⱽᴰ-square-from
      ⇒ⱽᴰ-square-isoᴰ .snd .secᴰ = Cᴰ.rectifyOut ⇒ⱽᴰ-square-sec
      ⇒ⱽᴰ-square-isoᴰ .snd .retᴰ = Cᴰ.rectifyOut ⇒ⱽᴰ-square-ret

    LHS-F RHS-F : Functor (Cᴰ / (C [-, A⇒B .vertex ])) (Cᴰ / (C [-, B ]))
    LHS-F = ((Idᴰ /Fⱽ yoRec (C [-, B ]) (element A⇒B)) ∘F ×LRⱽPshᴰ (LRⱽObᴰ→LRⱽ Cᴰ (Aᴰ[π₂] .fst , Aᴰ[π₂]-lrⱽ))) ∘F wkF (π₁Quadrable Cᴰ A ×A π₁-Quadrable) (vertex A⇒B)
    RHS-F = (×ᴰPᴰ ((C [-, A ]) , ×A) ((Cᴰ [-][-, Aᴰ ]) , ×Aᴰ) ∘F (Idᴰ /Fⱽ yoRec (((C [-, A ]) , ×A) ⇒PshSmall (C [-, B ])) (element A⇒B)))

    module _
      ((Δ , Δᴰ , f) (Γ , Γᴰ , g) : ((Cᴰ / (C [-, A⇒B .vertex ]))) .ob)
      ((γ , γᴰ , γg≡f) : ((Cᴰ / (C [-, A⇒B .vertex ]))) [ (Δ , Δᴰ , f) , (Γ , Γᴰ , g) ])
      where
      ⇒ⱽᴰ-square-nat :
       ((Fstⱽ Cᴰ (Element (C [-, B ])) ∘Fⱽᴰ Unitᴰ.recᴰ (compSectionFunctor Snd LHS-F)) .F-homᴰ {f = (γ , γᴰ , γg≡f)} _ Cᴰ.⋆ᴰ ⇒ⱽᴰ-square-to Γ Γᴰ g)
        Cᴰ.∫≡
       (⇒ⱽᴰ-square-isoᴰ Δ Δᴰ f .fst Cᴰ.⋆ᴰ (Fstⱽ Cᴰ (Element (C [-, B ])) ∘Fⱽᴰ Unitᴰ.recᴰ (compSectionFunctor Snd RHS-F)) .F-homᴰ {f = (γ , γᴰ , γg≡f)} _)
      ⇒ⱽᴰ-square-nat = ×ᴰAᴰ.×-extensionalityᴰ
        (⋆to-β₁ Γ Γᴰ g _ ∙ Cᴰ.⟨ ×ⱽπ₂*Aᴰ.β₁ⱽ _ _ ⟩⋆⟨⟩
        ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ π₁*.βᴰ' _ ∙ Cᴰ.reind-filler⁻ _ ⟩
        ∙ sym (to⋆-β₁ Δ Δᴰ f γᴰ))
        (⋆to-β₂ Γ Γᴰ g _
        ∙ Cᴰ.⟨ Cᴰ.reind-filler _ ∙ ×ⱽπ₂*Aᴰ.β₂ⱽ _ _ ∙ Cᴰ.reind-filler⁻ _ ∙ Cᴰ.reind-filler⁻ _ ⟩⋆⟨⟩
        ∙ sym (to⋆-β₂ Δ Δᴰ f γᴰ))

    ⇒ⱽᴰ-square :
      NatIso {C = Cᴰ / (C [-, A⇒B .vertex ])}
             {D = Cᴰ / (C [-, B ])}
             LHS-F
             RHS-F
    ⇒ⱽᴰ-square = /NatIso
      (record { trans = natTrans (λ x → C.id) λ f → C.⋆IdR _ ; nIso = λ _ → idCatIso .snd })
      (isosToNatIsoᴰ _ _ _
        (λ {(Γ , Γᴰ , f)} _ → ⇒ⱽᴰ-square-isoᴰ Γ Γᴰ f)
        λ {(Δ , Δᴰ , f) (Γ , Γᴰ , g) _ _ (γ , γᴰ , γg≡f)}  _ → ⇒ⱽᴰ-square-nat (Δ , Δᴰ , f) (Γ , Γᴰ , g) (γ , γᴰ , γg≡f))
      λ (Γ , Γᴰ , f) → C.⋆IdL _
    ∀+Expⱽ+lifts⇒Expᴰ : Exponentialᴰ Cᴰ (A , ×A) (Aᴰ , ×Aᴰ) Bᴰ A⇒B
    ∀+Expⱽ+lifts⇒Expᴰ =
      Representableⱽ→UniversalElementᴰ Cᴰ _ _ _ $
        ∀⟨Aᴰ[π₂]⇒Bᴰ[app]⟩ ◁PshIsoⱽ
        reindPshIso _ (Aᴰ[π₂]⇒Bᴰ[app] .snd ⋆PshIso reindPshIso _ (Bᴰ[app] .snd) ⋆PshIso (reindPsh∘F≅ _ _ _))
        ⋆PshIso reindPsh-square _ _ _ _ _ ⇒ⱽᴰ-square
