{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Reindex.ChosenReind where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.ChosenReind
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Section.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Functor
open Functorᴰ

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D) ⦃ cr : ChosenReind Dᴰ ⦄
  where
  private
    module C = Category C
    module D = Category D
    module Dᴰ = ChosenReindNotation Dᴰ

  reindexChosenReind : Categoryᴰ C ℓDᴰ ℓDᴰ'
  reindexChosenReind .Categoryᴰ.ob[_] x = Dᴰ.ob[ F ⟅ x ⟆ ]
  reindexChosenReind .Categoryᴰ.Hom[_][_,_] f a b = Dᴰ.Hom[ F ⟪ f ⟫ ][ a , b ]
  reindexChosenReind .Categoryᴰ.idᴰ = Dᴰ.reind⟨ sym (F .F-id) ⟩ Dᴰ.idᴰ
  reindexChosenReind .Categoryᴰ._⋆ᴰ_ {f = f} {g = g} fᴰ gᴰ =
    Dᴰ.reind⟨ sym (F .F-seq f g) ⟩ (fᴰ Dᴰ.⋆ᴰ gᴰ)
  reindexChosenReind .Categoryᴰ.⋆IdLᴰ fᴰ = Dᴰ.rectifyOut
    (Dᴰ.reind-∫≡ _ _ ∙ Dᴰ.⟨ Dᴰ.reind-∫≡ _ _ ⟩⋆⟨ refl ⟩ ∙ Dᴰ.⋆IdL (_ , fᴰ))
  reindexChosenReind .Categoryᴰ.⋆IdRᴰ fᴰ = Dᴰ.rectifyOut
    (Dᴰ.reind-∫≡ _ _ ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.reind-∫≡ _ _ ⟩ ∙ Dᴰ.⋆IdR (_ , fᴰ))
  reindexChosenReind .Categoryᴰ.⋆Assocᴰ fᴰ gᴰ hᴰ = Dᴰ.rectifyOut
    (Dᴰ.reind-∫≡ _ _
    ∙ Dᴰ.⟨ Dᴰ.reind-∫≡ _ _ ⟩⋆⟨ refl ⟩
    ∙ Dᴰ.⋆Assoc (_ , fᴰ) (_ , gᴰ) (_ , hᴰ)
    ∙ sym Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.reind-∫≡ _ _ ⟩
    ∙ sym (Dᴰ.reind-∫≡ _ _))
  reindexChosenReind .Categoryᴰ.isSetHomᴰ = Dᴰ.isSetHomᴰ

  instance
    reindexReind : ChosenReind reindexChosenReind
    reindexReind .ChosenReind.reind⟨_⟩ e = Dᴰ.reind⟨ cong (F ⟪_⟫) e ⟩
    reindexReind .ChosenReind.reind-filler e = Dᴰ.reind-filler (cong (F ⟪_⟫) e)

  πChosenReind : Functorᴰ F reindexChosenReind Dᴰ
  πChosenReind .F-obᴰ x = x
  πChosenReind .F-homᴰ fᴰ = fᴰ
  πChosenReind .F-idᴰ = symP (Dᴰ.reind-filler _ _)
  πChosenReind .F-seqᴰ fᴰ gᴰ = symP (Dᴰ.reind-filler _ _)

  π-FFᴰChosenReind : FullyFaithfulᴰ πChosenReind
  π-FFᴰChosenReind f xᴰ yᴰ = (λ z → z) , (λ _ → refl) , (λ _ → refl)

  GlobalSectionReindex→SectionChosenReind : GlobalSection reindexChosenReind →
    Section F Dᴰ
  GlobalSectionReindex→SectionChosenReind = compFunctorᴰGlobalSection
    πChosenReind
