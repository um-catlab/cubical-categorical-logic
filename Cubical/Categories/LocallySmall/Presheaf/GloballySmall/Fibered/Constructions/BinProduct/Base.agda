{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Presheaf.GloballySmall.Fibered.Constructions.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Presheaf.GloballySmall.Fibered.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
  renaming (π₁ to ×Cπ₁ ; π₂ to ×Cπ₂)
open import Cubical.Categories.LocallySmall.Bifunctor.Base
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.Fibered

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Bisection
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base
open import Cubical.Categories.LocallySmall.Displayed.Bifunctor.Base

open Category
open Categoryᴰ
open Σω
open Liftω

module _ (C : SmallCategory ℓC ℓC') where
  private
    module C = SmallCategory C
    module SET = CategoryᴰNotation SET
    PSHC = PRESHEAF C
    module PSHC = CategoryᴰNotation PSHC

  open Functorᴰ
  PshProd' : Functorᴰ ℓ-MAX (PSHC ×Cᴰ PSHC) PSHC
  PshProd' =
    FIBERED-FUNCTOR→FIBERED-FUNCTOR-EQ (C ^opsmall) SET Eq.refl
    ∘Fᴰ (postcomposeF _ _ ×SET
    ∘Fᴰ (,F-SFFunctorⱽ (C ^opsmall) SET SET
    ∘Fᴰ introF-×Cᴰ (×Cπ₁ _ _) (×Cπ₂ _ _)
      (FIBERED-FUNCTOR-EQ→FIBERED-FUNCTOR (C ^opsmall) SET Eq.refl
        ∘Fᴰ π₁ᴰ _ _)
      (FIBERED-FUNCTOR-EQ→FIBERED-FUNCTOR (C ^opsmall) SET Eq.refl
        ∘Fᴰ π₂ᴰ _ _)))

  PshProdᴰ : Bifunctorᴰ (ParFunctorToBifunctor ℓ-MAX) PSHC PSHC PSHC
  PshProdᴰ = ParFunctorᴰToBifunctorᴰ PshProd'

  PshProd : Bifunctor PSHC.∫C PSHC.∫C PSHC.∫C
  PshProd = Bifunctorᴰ.∫F PshProdᴰ

  open Bifunctor
  _×Psh_ : Presheaf C ℓP → Presheaf C ℓQ → Presheaf C (ℓ-max ℓP ℓQ)
  P ×Psh Q = PshProd .Bif-ob (_ , P) (_ , Q) .snd

  open FibNatTransDefs (C ^opsmall) SET
  open FibNatTrans
  module _ (P : Presheaf C ℓP)(Q : Presheaf C ℓQ) where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    open Functor
    π₁ : PshHom (P ×Psh Q) P
    π₁ .N-ob = λ _ → fst
    π₁ .N-hom {x = x} {y = y} f =
     SET.≡out
       {xᴰ = (P ×Psh Q) .F-ob (liftω x)} {yᴰ = P .F-ob (liftω y)}
       (sym $ SET.reind-filler
         {xᴰ = (P ×Psh Q) .F-ob (liftω x)} {yᴰ = P .F-ob (liftω y)}
         refl _)
    -- This goal is indeed a simple transportRefl, but I'm not
    -- sure what the most general strategy ought to be when
    -- proving naturality of arbitary PshHoms
    -- We should have a bridge between the naturality proofs needed
    -- for these PshHoms and the naturality proofs in the manual
    -- definition of PshHom for small presheaves.
    -- That is, the corresponding constructions of π₁ in
    -- Presheaf.Constructions.BinProduct.Base has N-hom via refl,
    -- and in LocallySmall.Presheaf.GloballySmall.Fibered.Base we
    -- have shown a definitional isomorphism between the two notions
    -- of presheaf, so we should be able to have an interface for proving the
    -- above N-hom that also only mentions refl

    π₂ : PshHom (P ×Psh Q) Q
    π₂ .N-ob = λ _ → snd
    π₂ .N-hom f = transportRefl _

  module _
    {P : Presheaf C ℓP}
    {Q : Presheaf C ℓQ}
    {R : Presheaf C ℓR}
    (α : PshHom R P)
    (β : PshHom R Q)
    where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q

    ×PshIntro : PshHom {C = C} R (P ×Psh Q)
    ×PshIntro .N-ob c x = α .N-ob c x , β .N-ob c x
    ×PshIntro .N-hom f =
      funExt λ p →
        (λ i → α .N-hom f i p , β .N-hom f i p)
        ∙ ΣPathP (
          (transportRefl _
           ∙ P.⟨⟩⋆⟨ sym $ transportRefl _ ⟩
           ∙ (sym $ transportRefl _)
           ∙ (sym $ transportRefl _)) ,
          transportRefl _
           ∙ Q.⟨⟩⋆⟨ sym $ transportRefl _ ⟩
           ∙ (sym $ transportRefl _)
           ∙ (sym $ transportRefl _))

    ×Pshβ₁ : ×PshIntro PSHC.⋆ᴰ π₁ P Q PSHC.∫≡ α
    ×Pshβ₁ = makeFibNatTransPath refl (λ _ → refl)

    ×Pshβ₂ : ×PshIntro PSHC.⋆ᴰ π₂ P Q PSHC.∫≡ β
    ×Pshβ₂ = makeFibNatTransPath refl (λ _ → refl)

  -- TODO to speed things up, make ⋆PshHom notation
  -- or make the homs in the presheaf category opaque
  -- because cmoposition in PSHC is quite slow
  --
  -- module _ (P : Presheaf C ℓP)(Q : Presheaf C ℓQ) where
  --   ×Psh-UMP :
  --     ∀ {R : Presheaf C ℓR} →
  --     Iso (PshHom {C = C} R (P ×Psh Q))
  --         (PshHom {C = C} R P × PshHom {C = C} R Q)
  --   ×Psh-UMP .Iso.fun α = (α PSHC.⋆ᴰ π₁ P Q) , {!!}
  --   ×Psh-UMP .Iso.inv = {!!}
  --   ×Psh-UMP .Iso.rightInv = {!!}
  --   ×Psh-UMP .Iso.leftInv = {!!}
  --   -- ×Psh-UMP .Iso.fun α = (α PSHC.⋆ᴰ π₁ P Q) , (α PSHC.⋆ᴰ π₂ P Q)
  --   -- ×Psh-UMP .Iso.inv (α , β) = ×PshIntro α β
  --   -- ×Psh-UMP .Iso.rightInv (α , β) =
  --   --   ΣPathP ((×Pshβ₁ α β) , (×Pshβ₂ α β))
  --   -- ×Psh-UMP .Iso.leftInv α = makeFibNatTransPath refl (λ _ → refl)
