module Cubical.Categories.LocallySmall.Instances.Functor.IntoFiberCategory.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Functor.IntoFiberCategory.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
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
    module FuncD = NatTransDefs D Eᴰ
    module FuncC = NatTransDefs C Eᴰ
    module NatTransD = FuncD.NatTrans
    module NatTransC = FuncC.NatTrans

  precomposeF : Functorⱽ (FUNCTOR D Eᴰ) (FUNCTOR C Eᴰ)
  precomposeF .F-obᴰ = _∘F F
  precomposeF .F-homᴰ α .NatTransC.N-ob c =
    α .NatTransD.N-ob (F-ob F (liftω c) .Liftω.lowerω)
  precomposeF .F-homᴰ α .NatTransC.N-hom f = α .NatTransD.N-hom (F-hom F f)
  precomposeF .F-idᴰ = FuncC.makeNatTransPath refl (λ _ → refl)
  precomposeF .F-seqᴰ _ _ = FuncC.makeNatTransPath refl (λ _ → refl)

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

    module FuncDᴰ = NatTransDefs C Dᴰ
    module FuncEᴰ = NatTransDefs C Eᴰ
    module NatTransDᴰ = FuncDᴰ.NatTrans
    module NatTransEᴰ = FuncEᴰ.NatTrans

  postcomposeF : Functorᴰ F (FUNCTOR C Dᴰ) (FUNCTOR C Eᴰ)
  postcomposeF .F-obᴰ G = Fv Fᴰ _ ∘F G
  postcomposeF .F-homᴰ α .NatTransEᴰ.N-ob c = Fᴰ.F-homᴰ (α .NatTransDᴰ.N-ob c)
  postcomposeF .F-homᴰ {xᴰ = G}{yᴰ = H} α .NatTransEᴰ.N-hom f =
      Eᴰ.⟨ sym $ Eᴰ.reind-filler _ _ ⟩⋆⟨⟩
      ∙ (sym $ Fᴰ.F-seqᴰ _ _)
      ∙ Fᴰ.F-homᴰ⟨ NatTransDᴰ.N-hom α f ⟩
      ∙ Fᴰ.F-seqᴰ _ _
      ∙ Eᴰ.⟨⟩⋆⟨ Eᴰ.reind-filler _ _ ⟩
  postcomposeF .F-idᴰ =
    FuncEᴰ.makeNatTransPath F.F-id λ _ → Fᴰ.F-idᴰ
  postcomposeF .F-seqᴰ _ _ =
    FuncEᴰ.makeNatTransPath (F.F-seq _ _) λ _ → Fᴰ.F-seqᴰ _ _
