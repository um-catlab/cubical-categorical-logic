{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Instances.Functor.SmallFibers.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
import Cubical.Categories.Functor as SmallF
import Cubical.Categories.NaturalTransformation as SmallNT

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Category.HLevels
import Cubical.Categories.LocallySmall.Functor.Base as LocallySmallF
import Cubical.Categories.LocallySmall.Functor.IntoFiberCategory as IntoFibCat
import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory as IntoFibCatNatTrans
open import Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibers
open import Cubical.Categories.LocallySmall.Functor.SmallFibers
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.Instances.Unit
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.LocallySmall.Displayed.Fibration.IsoFibration

open Category
open Categoryᴰ
open SmallCategory

module _
  {C : SmallCategory ℓC ℓC'}
  {D : SmallCategory ℓD ℓD'}
  where
  private
    module C = SmallCategory C
    module D = SmallCategory D
  module _
    {Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ}
    (Cᴰ : SmallFibersCategoryᴰ C.cat Cobᴰ-ℓ Cobᴰ CHom-ℓᴰ)
    {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
    (Dᴰ : SmallFibersCategoryᴰ D.cat Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
    where
    private
      module Cᴰ = CategoryᴰNotation Cᴰ
      module Dᴰ = CategoryᴰNotation Dᴰ

    open NatTransDefs Cᴰ Dᴰ
    open opIsoLift
    open CatIsoᴰ

    module _ (hasContrHomsC : hasContrHoms C.cat) where
      module _ (isoOpFibCᴰ : isIsoOpFibration Cᴰ) where
        -- This construction is completed but it isn't actually
        -- the correct generalization of presheaves over
        -- a presheaf category
        --
        -- We can't instantiate this construction where
        -- Cᴰ is a category of presheaves, as it does not have this
        -- isoOpFibration property over LEVEL
        -- I'd then thought that it would be sufficient to
        -- restrict to a category of levels that only has morphisms
        -- that respect the ordering between levels. That is,
        -- restrict to only the morphisms for which these opCartesian
        -- isoLifts exists. That's very nearly the right definition, however
        -- then the category of levels no longer has contractible homs
        FUNCTOR : Categoryᴰ (SmallCategory.cat ((C ^opsmall) ×Csmall D))
          (λ (liftω (c , d)) → Functor c d)
          _
        FUNCTOR .Hom[_][_,_] f = NatTrans hasContrHomsC isoOpFibCᴰ (f .snd)
        FUNCTOR .idᴰ = idTrans hasContrHomsC isoOpFibCᴰ _
        FUNCTOR ._⋆ᴰ_ = seqTrans hasContrHomsC isoOpFibCᴰ
        FUNCTOR .⋆IdLᴰ {xᴰ = F} {yᴰ = G} α =
          ΣPathP (ΣPathP ((isContr→isProp (hasContrHomsC _ _) _ _) , refl) , refl)
          ∙ makeNatTransPath hasContrHomsC isoOpFibCᴰ (D.⋆IdL _) (λ x →
            Dᴰ.⟨⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _) ⟩
            ∙ (sym $ Dᴰ.⋆Assocᴰ _ _ _)
            ∙ Dᴰ.⟨ IntoFibCatNatTrans.NatTransDefs.NatTrans.N-hom α _ ⟩⋆⟨⟩
            ∙ Dᴰ.⋆Assocᴰ _ _ _
            ∙ Dᴰ.⟨⟩⋆⟨
               Dᴰ.reind-filler _ _
               ∙ Dᴰ.≡in (sym $ G.F-seq _ _)
               ∙ Dᴰ.≡in G.F-hom⟨
                 Cᴰ.rectify $ Cᴰ.≡out $
                   (sym $ Cᴰ.reind-filler _ _ )
                   ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
                   ∙ Cᴰ.⋆Assocᴰ _ _ _
                   ∙ Cᴰ.⟨⟩⋆⟨ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                             ∙ Cᴰ.⟨ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .retᴰ ⟩⋆⟨⟩
                             ∙ Cᴰ.⋆IdLᴰ _ ⟩
                   ∙ Cᴰ.⋆Assocᴰ _ _ _
                   ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩ ⟩
                   ∙ Cᴰ.⟨⟩⋆⟨ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                             ∙ Cᴰ.⟨ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .retᴰ ⟩⋆⟨⟩
                             ∙ Cᴰ.⋆IdLᴰ _ ⟩
                   ∙ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .secᴰ
                   ∙ Cᴰ.reind-filler _ _
                 ⟩
               ⟩
            ∙ Dᴰ.⟨⟩⋆⟨ Dᴰ.≡in G.F-id ∙ (sym $ Dᴰ.reind-filler _ _) ⟩
            ∙ Dᴰ.⋆IdRᴰ _)
          ∙ ΣPathP (ΣPathP ((isContr→isProp (hasContrHomsC _ _) _ _) , refl) , refl)
           where
           module G = LocallySmallF.FunctorNotation G

        FUNCTOR .⋆IdRᴰ {xᴰ = F} {yᴰ = G} α =
          ΣPathP (ΣPathP ((isContr→isProp (hasContrHomsC _ _) _ _) , refl) , refl)
          ∙ makeNatTransPath hasContrHomsC isoOpFibCᴰ (D.⋆IdR _) (λ x →
              Dᴰ.⟨⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
              ∙ Dᴰ.⟨⟩⋆⟨
                Dᴰ.reind-filler _ _
                ∙ (Dᴰ.≡in $ sym $ G.F-seq _ _)
                ∙ Dᴰ.≡in G.F-hom⟨
                    Cᴰ.rectify $ Cᴰ.≡out $
                      (sym $ Cᴰ.reind-filler _ _)
                      ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
                      ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                      ∙ Cᴰ.⟨ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .retᴰ
                           ⟩⋆⟨ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .secᴰ ⟩
                      ∙ Cᴰ.⋆IdLᴰ _
                      ∙ Cᴰ.reind-filler _ _
                  ⟩
                ∙ Dᴰ.≡in G.F-id
                ∙ (sym $ Dᴰ.reind-filler _ _)
              ⟩
              ∙ Dᴰ.⋆IdRᴰ _)
          ∙ ΣPathP (ΣPathP ((isContr→isProp (hasContrHomsC _ _) _ _) , refl) , refl)
           where
           module G = LocallySmallF.FunctorNotation G

        FUNCTOR .⋆Assocᴰ {xᴰ = F} {yᴰ = G} {zᴰ = H} {wᴰ = K} α β γ =
          ΣPathP (ΣPathP ((isContr→isProp (hasContrHomsC _ _) _ _) , refl) , refl)
          ∙ makeNatTransPath hasContrHomsC isoOpFibCᴰ (D.⋆Assoc _ _ _) (λ x →
              Dᴰ.⟨⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
              ∙ Dᴰ.⋆Assocᴰ _ _ _
              ∙ Dᴰ.⟨⟩⋆⟨
                  Dᴰ.⟨ sym $ Dᴰ.reind-filler _ _ ⟩⋆⟨⟩
                  ∙ Dᴰ.⋆Assocᴰ _ _ _
                  ∙ Dᴰ.⟨⟩⋆⟨
                     (sym $ Dᴰ.⋆Assocᴰ _ _ _)
                     ∙ Dᴰ.⟨ IntoFibCatNatTrans.NatTransDefs.NatTrans.N-hom γ
                             (SmallNT.NatTrans.N-ob (LiftF-seq hasContrHomsC isoOpFibCᴰ) x) ⟩⋆⟨⟩
                     ∙ Dᴰ.⋆Assocᴰ _ _ _
                     ∙ Dᴰ.⟨⟩⋆⟨
                        Dᴰ.reind-filler _ _
                        ∙ (Dᴰ.≡in $ sym $ K.F-seq _ _)
                        ∙ (Dᴰ.≡in $ K.F-hom⟨
                             Cᴰ.rectify $ Cᴰ.≡out $
                               (sym $ Cᴰ.reind-filler _ _)
                               ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩
                               ∙ Cᴰ.⋆Assocᴰ _ _ _
                               ∙ Cᴰ.⋆Assocᴰ _ _ _
                               ∙ Cᴰ.⟨⟩⋆⟨
                                   Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩
                                   ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                                   ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                                   ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                                   ∙ Cᴰ.⟨
                                      Cᴰ.⋆Assocᴰ _ _ _
                                      ∙ Cᴰ.⋆Assocᴰ _ _ _
                                      ∙ Cᴰ.⋆Assocᴰ _ _ _
                                      ∙ Cᴰ.⟨⟩⋆⟨
                                         Cᴰ.⋆Assocᴰ _ _ _
                                         ∙ Cᴰ.⟨⟩⋆⟨
                                           Cᴰ.⟨⟩⋆⟨
                                              (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                                              ∙ Cᴰ.⟨ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .retᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdLᴰ _ ⟩
                                           ∙ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .retᴰ
                                           ⟩
                                         ∙ Cᴰ.⋆IdRᴰ _
                                       ⟩
                                      ∙ Cᴰ.⟨ (sym $ Cᴰ.⋆IdRᴰ _)
                                             ∙ Cᴰ.⟨⟩⋆⟨ sym $ isoOpFibCᴰ _ _ .f*cᴰIsoᴰ .retᴰ ⟩
                                             ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _) ⟩⋆⟨⟩
                                      ⟩⋆⟨⟩
                                   ∙ Cᴰ.⋆Assocᴰ _ _ _
                                   ∙ Cᴰ.⋆Assocᴰ _ _ _
                                 ⟩
                               ∙ (sym $ Cᴰ.⋆Assocᴰ _ _ _)
                               ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
                               ∙ Cᴰ.reind-filler _ _
                           ⟩)
                        ∙ (Dᴰ.≡in $ K.F-seq _ _)
                        ∙ (sym $ Dᴰ.reind-filler _ _)
                       ⟩
                     ∙ (sym $ Dᴰ.⋆Assocᴰ _ _ _)
                   ⟩
                  ∙ (sym $ Dᴰ.⋆Assocᴰ _ _ _)
                ⟩
              ∙ Dᴰ.⟨⟩⋆⟨ Dᴰ.⟨ Dᴰ.⟨⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩ ⟩⋆⟨⟩
                        ∙ Dᴰ.reind-filler _ _ ⟩ )
          ∙ ΣPathP (ΣPathP ((isContr→isProp (hasContrHomsC _ _) _ _) , refl) , refl)

           where
           module K = LocallySmallF.FunctorNotation K

        FUNCTOR .isSetHomᴰ =
          IntoFibCatNatTrans.NatTransDefs.isSetNatTrans _ _ _ _ _
