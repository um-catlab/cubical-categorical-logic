module Cubical.Categories.LocallySmall.Instances.Functor.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Functor.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Category
open Categoryᴰ

open Functor
open SmallFibNatTrans
open Functorᴰ

module _
  {C : SmallCategory ℓC ℓC'}
  {D : SmallCategory ℓD ℓD'}
  (F : Functor (SmallCategory.cat C) (SmallCategory.cat D))
  {Eobᴰ-ℓ Eobᴰ EHom-ℓᴰ}
  {E : Category Eob EHom-ℓ}
  (Eᴰ : SmallFibersCategoryᴰ E Eobᴰ-ℓ Eobᴰ EHom-ℓᴰ)
  where

  precomposeF : Functorⱽ (FIBER-FUNCTOR D Eᴰ) (FIBER-FUNCTOR C Eᴰ)
  precomposeF .F-obᴰ G = G ∘F F
  precomposeF .F-homᴰ α .N-ob c = α .N-ob (F-ob F (liftω c) .Liftω.lowerω)
  precomposeF .F-homᴰ α .N-hom = λ f₁ → α .N-hom (F-hom F f₁)
  precomposeF .F-idᴰ = makeSFNatTransPath refl (λ _ → refl)
  precomposeF .F-seqᴰ _ _ = makeSFNatTransPath refl (λ _ → refl)

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
    module Fᴰ = FunctorᴰNotation Fᴰ
    module Eᴰ = CategoryᴰNotation Eᴰ

  postcomposeF : Functorᴰ F (FIBER-FUNCTOR C Dᴰ) (FIBER-FUNCTOR C Eᴰ)
  postcomposeF .F-obᴰ G = Fv Fᴰ _ ∘F G
  postcomposeF .F-homᴰ α .N-ob c = Fᴰ.F-homᴰ (α .N-ob c)
  postcomposeF .F-homᴰ {xᴰ = G}{yᴰ = H} α .N-hom f =
    N-hom'→N-hom Eᴰ _ (Fv Fᴰ _ ∘F G) (Fv Fᴰ _ ∘F H) _ f $
      Eᴰ.⟨ sym $ Eᴰ.reind-filler _ _ ⟩⋆⟨⟩
      ∙ (sym $ Fᴰ.F-seqᴰ _ _)
      ∙ Fᴰ.F-homᴰ⟨ N-hom' α f ⟩
      ∙ Fᴰ.F-seqᴰ _ _
      ∙ Eᴰ.⟨⟩⋆⟨ Eᴰ.reind-filler _ _ ⟩
  postcomposeF .F-idᴰ = makeSFNatTransPath F.F-id λ _ → Fᴰ.F-idᴰ
  postcomposeF .F-seqᴰ _ _ =
    makeSFNatTransPath (F.F-seq _ _) λ _ → Fᴰ.F-seqᴰ _ _
