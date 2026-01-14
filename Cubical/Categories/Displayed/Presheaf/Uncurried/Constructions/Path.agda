{-# OPTIONS --lossy-unification #-}
{- TODO: split up this file into a bunch of individual construction files -}

{-

  Every construction on presheaves should come with
  1. A UMP which provides an interface to it
  2. A reindexing lemma that shows that it commutes with reindPshᴰNatTrans in the appropriate sense

-}

module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Sigma.More as Type
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.Reind
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Functors.Constant.More
open import Cubical.Categories.FunctorComprehension.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory as TotalCat hiding (intro)
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions hiding (ΣPsh)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions.RightAdjoint
open import Cubical.Categories.Profunctor.Constructions.Extension
open import Cubical.Categories.Yoneda.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
import Cubical.Categories.Displayed.Presheaf.Constructions.Curry as Curry
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Sigma

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓS ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ ℓSᴰ : Level

open Category
open Functor
open Functorᴰ
open Iso
open PshHom
open PshIso

-- Products
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ (P : Presheaf C ℓP) where
    private
      module P = PresheafNotation P
    opaque
      unfolding PshHet→ElementFunctorᴰ
      PathPsh' : Functor ((∫C (Element (P ×Psh P))) ^op) (PROP ℓP)
      PathPsh' = mkFunctor (PROP _) hasPropHomsPROP (λ (_ , p , p') → (p ≡ p') , P.isSetPsh p p')
        λ {(x , p , p')} {(y , q , q')} (f , fp,fp'≡q,q') p≡p' →
          (sym $ PathPΣ fp,fp'≡q,q' .fst) ∙ cong (f P.⋆_) p≡p' ∙ PathPΣ fp,fp'≡q,q' .snd

      PathPsh : Presheafᴰ (P ×Psh P) Cᴰ ℓP
      PathPsh = PROP→SET ∘F PathPsh' ∘F (∫F {F = Id} (Sndⱽ Cᴰ (Element (P ×Psh P))) ^opF)

      -- TODO: general isPropPsh
      Refl : PshHomᴰ ΔPshHom (UnitPsh {C = Cᴰ / P}) PathPsh
      Refl = pshhom (λ _ _ → refl) (λ _ _ _ _ → P.isSetPsh _ _ _ _)

    module _ {Rᴰ : Presheafᴰ (P ×Psh P) Cᴰ ℓRᴰ} where
      private
        module Rᴰ = PresheafᴰNotation Cᴰ (P ×Psh P) Rᴰ
      opaque
        unfolding PathPsh PresheafᴰNotation.∫
        PathPsh-rec : PshHomᴰ ΔPshHom UnitPsh Rᴰ → PshHomⱽ PathPsh Rᴰ
        PathPsh-rec αⱽ .N-ob (x , xᴰ , p , q) p≡q =
          -- should I use formal-reind instead of reind?
          Rᴰ.reind (ΣPathP (refl , p≡q)) (αⱽ .N-ob (x , xᴰ , p) tt)
        PathPsh-rec αⱽ .N-hom (Δ , Δᴰ , (p , q)) (Γ , Γᴰ , (p' , q')) (γ , γᴰ , γ⋆p,γ⋆q≡p',q') p≡q = Rᴰ.rectify $ Rᴰ.≡out $
          (sym $ Rᴰ.reind-filler _)
          ∙ Rᴰ.≡in (αⱽ .N-hom _ _  (γ , (γᴰ , (PathPΣ γ⋆p,γ⋆q≡p',q' .fst))) tt)
          ∙ Rᴰ.⋆ᴰ-reind _ _ _
          ∙ Rᴰ.⟨⟩⋆⟨ Rᴰ.reind-filler _ ⟩
          ∙ sym (Rᴰ.⋆ᴰ-reind _ _ _)

        -- UMP:
        --   p ≡ p' ⊢ Qᴰ(p,p')
        -- =====================
        --   * ⊢ Qᴰ(p,p)
        PathPsh-UMP : Iso (PshHomⱽ PathPsh Rᴰ) (PshHomᴰ ΔPshHom UnitPsh Rᴰ)
        PathPsh-UMP = iso
          (λ αⱽ → Refl ⋆PshHom reindPshHom (Idᴰ /Fⱽ ΔPshHom) αⱽ)
          PathPsh-rec
          (λ αⱽ → makePshHomPath $ funExt λ (Γ , Γᴰ , p) → funExt λ _ → transportRefl _)
          λ αⱽ → makePshHomPath $ funExt λ (Γ , Γᴰ , (p , q)) → funExt λ p≡q →
            sym (Rᴰ.rectify $ Rᴰ.≡out $ (Rᴰ.≡in $ (λ i → αⱽ .N-ob (Γ , (Γᴰ , (p , (p≡q (~ i))))) (λ j → p≡q ((~ i) ∧ j)))) ∙ Rᴰ.reind-filler _)

opaque
  unfolding PathPsh unfoldPresheafᴰDefs PathPsh-rec
  unfoldPathDefs : Unit
  unfoldPathDefs = tt
