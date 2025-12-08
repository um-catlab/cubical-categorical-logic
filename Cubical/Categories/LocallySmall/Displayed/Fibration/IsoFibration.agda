module Cubical.Categories.LocallySmall.Displayed.Fibration.IsoFibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.HLevels
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Instances.Indiscrete

open import Cubical.Categories.LocallySmall.Displayed.Category
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Category
open Functor
open Functorᴰ
open CatIso
open Liftω

module _
  {C : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = CategoryᴰNotation Cᴰ

  record IsoLift {c c'}
    (cᴰ : Cᴰ.Ob[ c' ]) (f : CatIso C c c') : Typeω
    where
    field
      f*cᴰ : Cᴰ.Ob[ c ]
      f*cᴰIsoᴰ : CatIsoᴰ Cᴰ f f*cᴰ cᴰ

  record opIsoLift {c c'}
    (cᴰ : Cᴰ.Ob[ c ]) (f : CatIso C c c') : Typeω
    where
    field
      f*cᴰ : Cᴰ.Ob[ c' ]
      f*cᴰIsoᴰ : CatIsoᴰ Cᴰ f cᴰ f*cᴰ

  isIsoFibration : Typeω
  isIsoFibration = ∀ {c c'} (cᴰ : Cᴰ.Ob[ c' ]) (f : CatIso C c c')
    → IsoLift cᴰ f

  isIsoOpFibration : Typeω
  isIsoOpFibration = ∀ {c c'} (cᴰ : Cᴰ.Ob[ c ]) (f : CatIso C c c')
    → opIsoLift cᴰ f

module _ {C : SmallCategory ℓC ℓC'} where
  private
    module C = SmallCategory C
  module _
    (hasContrHomsC : hasContrHoms C.cat)
    (Cᴰ : Categoryᴰ C.cat Cobᴰ CHom-ℓᴰ) where
    private
      module Cᴰ = CategoryᴰNotation Cᴰ

    module _
      (c c' : C.Ob)
      (opIsoLifts : (cᴰ : Cᴰ.Ob[ c ]) → opIsoLift Cᴰ cᴰ
        (mkContrHomsIso C.cat hasContrHomsC c c'))
      where
      open opIsoLift
      open CatIsoᴰ
      contrHomsIsoOpFibF : Functor Cᴰ.v[ c ] Cᴰ.v[ c' ]
      contrHomsIsoOpFibF .F-ob cᴰ = opIsoLifts cᴰ .f*cᴰ
      contrHomsIsoOpFibF .F-hom f =
        Cᴰ.reind (C.⟨ C.⋆IdR _ ⟩⋆⟨⟩ ∙ isContr→isProp (hasContrHomsC _ _) _ _)
          ((opIsoLifts _ .f*cᴰIsoᴰ .invᴰ Cᴰ.⋆ᴰ f) Cᴰ.⋆ᴰ opIsoLifts _ .f*cᴰIsoᴰ .funᴰ)
      contrHomsIsoOpFibF .F-id =
        Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ Cᴰ.⟨⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩ ∙ Cᴰ.⋆IdRᴰ _ ⟩⋆⟨⟩
          ∙ opIsoLifts _ .f*cᴰIsoᴰ .secᴰ
          ∙ Cᴰ.reind-filler _ _
      contrHomsIsoOpFibF .F-seq f g =
        Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ Cᴰ.⟨⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩ ⟩⋆⟨⟩
          ∙ Cᴰ.⟨ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                 ∙ Cᴰ.⟨ (sym $ Cᴰ.⋆IdRᴰ _)
                        ∙ Cᴰ.⟨⟩⋆⟨ sym $ opIsoLifts _ .f*cᴰIsoᴰ .retᴰ ⟩
                        ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _) ⟩⋆⟨⟩
                 ∙ Cᴰ.⋆Assocᴰ _ _ _ ⟩⋆⟨⟩
          ∙ (Cᴰ.⋆Assocᴰ _ _ _)
          ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
          ∙ Cᴰ.reind-filler _ _

module _ {CTy : Type ℓC} where
  private
    C = Indiscrete (Liftω CTy)
  module _ (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ) where
    private
      module C = CategoryNotation C
      module Cᴰ = CategoryᴰNotation Cᴰ
    module _
      (c c' : C.Ob)
      (opIsoLifts : (cᴰ : Cᴰ.Ob[ c ]) → opIsoLift Cᴰ cᴰ (mkIndiscreteIso c c'))
      where
      open opIsoLift
      open CatIsoᴰ
      IndiscreteIsoOpFibF : Functor Cᴰ.v[ c ] Cᴰ.v[ c' ]
      IndiscreteIsoOpFibF .F-ob cᴰ = opIsoLifts cᴰ .f*cᴰ
      IndiscreteIsoOpFibF .F-hom f =
        (opIsoLifts _ .f*cᴰIsoᴰ .invᴰ Cᴰ.⋆ᴰ f) Cᴰ.⋆ᴰ opIsoLifts _ .f*cᴰIsoᴰ .funᴰ
      IndiscreteIsoOpFibF .F-id =
        Cᴰ.rectify $ Cᴰ.≡out $
          Cᴰ.⟨ Cᴰ.⟨⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
              ∙ Cᴰ.⋆IdRᴰ _ ⟩⋆⟨⟩
          ∙ opIsoLifts _ .f*cᴰIsoᴰ .secᴰ
          ∙ Cᴰ.reind-filler _ _
      IndiscreteIsoOpFibF .F-seq f g =
        Cᴰ.rectify $ Cᴰ.≡out $
          Cᴰ.⟨ Cᴰ.⟨⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩ ⟩⋆⟨⟩
          ∙ Cᴰ.⟨ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                 ∙ Cᴰ.⟨ (sym $ Cᴰ.⋆IdRᴰ _)
                        ∙ Cᴰ.⟨⟩⋆⟨ sym $ opIsoLifts _ .f*cᴰIsoᴰ .retᴰ ⟩
                        ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _) ⟩⋆⟨⟩
                 ∙ Cᴰ.⋆Assocᴰ _ _ _ ⟩⋆⟨⟩
          ∙ (Cᴰ.⋆Assocᴰ _ _ _)
          ∙ Cᴰ.reind-filler _ _

module _ {CTy : Type ℓC} where
  private
    C = Indiscrete (Liftω CTy)
  module _ (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ) where
    private
      module C = CategoryNotation C
      module Cᴰ = CategoryᴰNotation Cᴰ

    open opIsoLift
    open CatIsoᴰ
    record WeakJoin (c c' : CTy) : Typeω where
      field
        weakJoin : CTy
        opIsoLiftL : ∀ (cᴰ : Cᴰ.Ob[ liftω c ]) →
          opIsoLift Cᴰ cᴰ (mkIndiscreteIso (liftω c) (liftω weakJoin))
        opIsoLiftR : ∀ (cᴰ' : Cᴰ.Ob[ liftω c' ]) →
          opIsoLift Cᴰ cᴰ' (mkIndiscreteIso (liftω c') (liftω weakJoin))

    WeakJoinsIsoOpFibration : Typeω
    WeakJoinsIsoOpFibration = ∀ c c' → WeakJoin c c'
