{-# OPTIONS --lossy-unification #-}
{- TODO: split up this file into a bunch of individual construction files -}

{-

  Every construction on presheaves should come with
  1. A UMP which provides an interface to it
  2. A reindexing lemma that shows that it commutes with reindPshᴰNatTrans in the appropriate sense

-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Sigma where

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

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ {P : Presheaf C ℓP}(Q : Presheaf C ℓQ)
    (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ) where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module Pᴰ = PresheafᴰNotation Cᴰ (P ×Psh Q) Pᴰ

    opaque
      unfolding PshHet→ElementFunctorᴰ PresheafᴰNotation.∫
      ΣPsh : Presheafᴰ P Cᴰ (ℓ-max ℓQ ℓPᴰ)
      ΣPsh .F-ob (Γ , Γᴰ , p) .fst = Σ[ q ∈ Q.p[ Γ ] ] Pᴰ.p[ p , q ][ Γᴰ ]
      ΣPsh .F-ob (Γ , Γᴰ , p) .snd = isSetΣ (Q .F-ob Γ .snd) (λ x → Pᴰ .F-ob (Γ , Γᴰ , p , x) .snd)
      ΣPsh .F-hom (γ , γᴰ , γ⋆p≡p') (q , pᴰ) = (γ Q.⋆ q) , Pᴰ .F-hom (γ , (γᴰ , (ΣPathP (γ⋆p≡p' , refl)))) pᴰ
      ΣPsh .F-id = funExt λ (q , pᴰ) → ΣPathP ((Q.⋆IdL q) , (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.⋆ᴰ-reind _ _ _ ∙ Pᴰ.⋆IdL _))
      ΣPsh .F-seq _ _ = funExt λ (q , pᴰ) → ΣPathP (Q.⋆Assoc _ _ _ , (Pᴰ.rectify $ Pᴰ.≡out $
        Pᴰ.⋆ᴰ-reind _ _ _ ∙ Pᴰ.⋆Assoc _ _ _
        ∙ Pᴰ.⟨⟩⋆⟨ sym (Pᴰ.⋆ᴰ-reind _ _ _) ⟩
        ∙ sym (Pᴰ.⋆ᴰ-reind _ _ _)))

      ΣPsh-σ : PshHomⱽ Pᴰ (wkPshᴰ Q ⟅ ΣPsh ⟆)
      ΣPsh-σ .N-ob (x , xᴰ , (p , q)) pᴰ = q , pᴰ
      ΣPsh-σ .N-hom (x , xᴰ , (p , q)) (x' , xᴰ' , (p' , q')) (f , fᴰ , f⋆p,f⋆q≡p',q') pᴰ =
        ΣPathP (((sym $ PathPΣ f⋆p,f⋆q≡p',q' .snd )) , (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.⋆ᴰ-reind _ _ _ ∙ sym (Pᴰ.⋆ᴰ-reind _ _ _)))

    -- TODO: reindΣ
    -- (p ↦ Σ[ q ] Pᴰ(p,q))[α] = Σ[ q ] Pᴰ(α(p), q)

    module _ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ} where
      private
        module Rᴰ = PresheafᴰNotation Cᴰ P Rᴰ
      opaque
        unfolding ΣPsh
        ΣPsh-rec : PshHomⱽ Pᴰ (wkPshᴰ Q ⟅ Rᴰ ⟆) → PshHomⱽ ΣPsh Rᴰ
        ΣPsh-rec α .N-ob (x , xᴰ , p) (q , pᴰ) = α .N-ob (x , xᴰ , p , q) pᴰ
        ΣPsh-rec α .N-hom (Δ , Δᴰ , p')(Γ , Γᴰ , p) (γ , γᴰ , γ⋆p≡p') (q , pᴰ) = α .N-hom _ _ _ _
          ∙ (Rᴰ.rectify $ Rᴰ.≡out $ Rᴰ.⋆ᴰ-reind _ _ _ ∙ (sym $ Rᴰ.⋆ᴰ-reind _ _ _))

        -- (Σ[ q ] Pᴰ(p,q) ⊢ Rᴰ(p)) ≅ Pᴰ(p,q) ⊢ Rᴰ(p)
        ΣPsh-UMP : Iso (PshHomⱽ ΣPsh Rᴰ) (PshHomⱽ Pᴰ (wkPshᴰ Q ⟅ Rᴰ ⟆))
        ΣPsh-UMP = iso (λ αⱽ → ΣPsh-σ ⋆PshHomⱽ reindPshHom (Idᴰ /Fⱽ π₁ P Q) αⱽ) ΣPsh-rec
          (λ αⱽ → makePshHomPath $ funExt λ (x , xᴰ , p , q) → funExt λ pᴰ → refl)
          λ αⱽ → makePshHomPath $ funExt λ (x , xᴰ , p) → funExt λ (q , pᴰ) → refl

opaque
  unfolding ΣPsh ΣPsh-rec unfoldPresheafᴰDefs
  unfoldΣDefs : Unit
  unfoldΣDefs = tt
