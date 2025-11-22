module Cubical.Categories.LocallySmall.Instances.Functor.Fibered.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.Fibered
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Functor.Properties

open Category
open Categoryᴰ

open Functor
open Functorᴰ

module _
  {C : SmallCategory ℓC ℓC'}
  {D : SmallCategory ℓD ℓD'}
  (F : Functor (SmallCategory.cat C) (SmallCategory.cat D))
  {Eobᴰ-ℓ Eobᴰ EHom-ℓᴰ}
  {E : Category Eob EHom-ℓ}
  (Eᴰ : SmallFibersCategoryᴰ E Eobᴰ-ℓ Eobᴰ EHom-ℓᴰ)
  where

  private
    module FibF-D = FibNatTransDefs D Eᴰ
    module FibF-C = FibNatTransDefs C Eᴰ
    module FibNT-D = FibF-D.FibNatTrans
    module FibNT-C = FibF-C.FibNatTrans

  precomposeF : Functorⱽ (FIBERED-FUNCTOR D Eᴰ) (FIBERED-FUNCTOR C Eᴰ)
  precomposeF .F-obᴰ = _∘F F
  precomposeF .F-homᴰ α .FibNT-C.N-ob c =
    α .FibNT-D.N-ob (F-ob F (liftω c) .Liftω.lowerω)
  precomposeF .F-homᴰ α .FibNT-C.N-hom f = α .FibNT-D.N-hom (F-hom F f)
  precomposeF .F-idᴰ = FibF-C.makeFibNatTransPath refl (λ _ → refl)
  precomposeF .F-seqᴰ _ _ = FibF-C.makeFibNatTransPath refl (λ _ → refl)

module _
  {C : SmallCategory ℓC ℓC'}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  {D : Category Dob DHom-ℓ}
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  {Eobᴰ-ℓ Eobᴰ EHom-ℓᴰ}
  {E : Category Eob EHom-ℓ}
  {F : Functor D E}
  (Eᴰ : SmallFibersCategoryᴰ E Eobᴰ-ℓ Eobᴰ EHom-ℓᴰ)
  (Fᴰ : Functorᴰ F Dᴰ Eᴰ)
  where
  private
    module F = FunctorNotation F
    module Fᴰ = Functorᴰ Fᴰ
    module Eᴰ = Categoryᴰ Eᴰ

    module FibF-Dᴰ = FibNatTransDefs C Dᴰ
    module FibF-Eᴰ = FibNatTransDefs C Eᴰ
    module FibNT-Dᴰ = FibF-Dᴰ.FibNatTrans
    module FibNT-Eᴰ = FibF-Eᴰ.FibNatTrans

  postcomposeF : Functorᴰ F (FIBERED-FUNCTOR C Dᴰ) (FIBERED-FUNCTOR C Eᴰ)
  postcomposeF .F-obᴰ G = Fv Fᴰ _ ∘F G
  postcomposeF .F-homᴰ α .FibNT-Eᴰ.N-ob c = Fᴰ.F-homᴰ (α .FibNT-Dᴰ.N-ob c)
  postcomposeF .F-homᴰ {xᴰ = G}{yᴰ = H} α .FibNT-Eᴰ.N-hom f =
    FibF-Eᴰ.N-hom'→N-hom (Fv Fᴰ _ ∘F G) (Fv Fᴰ _ ∘F H) _ f $
      Eᴰ.⟨ sym $ Eᴰ.reind-filler _ _ ⟩⋆⟨⟩
      ∙ (sym $ Fᴰ.F-seqᴰ _ _)
      ∙ Fᴰ.F-homᴰ⟨ FibNT-Dᴰ.N-hom' α f ⟩
      ∙ Fᴰ.F-seqᴰ _ _
      ∙ Eᴰ.⟨⟩⋆⟨ Eᴰ.reind-filler _ _ ⟩
  postcomposeF .F-idᴰ =
    FibF-Eᴰ.makeFibNatTransPath F.F-id λ _ → Fᴰ.F-idᴰ
  postcomposeF .F-seqᴰ _ _ =
    FibF-Eᴰ.makeFibNatTransPath (F.F-seq _ _) λ _ → Fᴰ.F-seqᴰ _ _
