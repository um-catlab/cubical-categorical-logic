{-# OPTIONS --lossy-unification #-}
{- TODO: split up this file into a bunch of individual construction files -}

{-

  Every construction on presheaves should come with
  1. A UMP which provides an interface to it
  2. A reindexing lemma that shows that it commutes with reindPshᴰNatTrans in the appropriate sense

-}

module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Rest where

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
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Path
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Push
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Pullback

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

module _ {C : Category ℓC ℓC'}(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  open UniversalElementNotation
  LocallyRepresentable∀ : Presheaf C ℓP → Type _
  LocallyRepresentable∀ P = Σ[ _×P ∈ LocallyRepresentable P ]
    (∀ {x}(xᴰ : Cᴰ.ob[ x ])
    → Representableⱽ Cᴰ ((x ×P) .vertex)
      (reindPshᴰNatTrans (yoRec (C [-, x ]) ((x ×P) .element .fst)) (Cᴰ [-][-, xᴰ ])))
    -- aka "π₁ is Quadrable"
  LR∀Presheaf : (ℓP : Level) → Type _
  LR∀Presheaf ℓP = Σ (Presheaf C ℓP) LocallyRepresentable∀

  module _ {P : Presheaf C ℓQ}((Q , _×Q , π₁*) : LR∀Presheaf ℓQ) where
    private
      module P = PresheafNotation P
      module P×Q = PresheafNotation (P ×Psh Q)
    LR∀-pullback : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
      → isPullbackSq
          (yoRec P p)
          (π₁ P Q)
          (yoRec (P ×Psh Q) (((Γ ×Q) .element .fst) P.⋆ p , (Γ ×Q) .element .snd))
          (yoRec (C [-, Γ ]) ((Γ ×Q) .element .fst))
    LR∀-pullback Γᴰ p .fst = yoInd P _ _ (P.⋆IdL _ ∙ P.⟨ sym $ C.⋆IdL _ ⟩⋆⟨⟩)
    LR∀-pullback Γᴰ p .snd Δ (p' , q) .fst (γ , p'≡γ⋆p) =
      intro (_ ×Q) (γ , q)
      , ΣPathP ( (p'≡γ⋆p ∙ P.⟨ sym (PathPΣ (β (_ ×Q)) .fst) ⟩⋆⟨⟩) ∙ P.⋆Assoc _ _ _
               , (sym $ PathPΣ (β (_ ×Q)) .snd))
    LR∀-pullback Γᴰ p .snd Δ (p' , q) .snd .fst (γ , p'≡γ⋆p) = ΣPathPProp (λ - → P.isSetPsh _ _) (PathPΣ (β (_ ×Q)) .fst)
    LR∀-pullback Γᴰ p .snd Δ (p' , q) .snd .snd (γ , p',q≡γ⋆π₁⋆p,γ⋆π₂) =
      ΣPathPProp
        (λ _ → P×Q.isSetPsh _ _)
        (intro≡ (_ ×Q) (ΣPathP (refl , (PathPΣ p',q≡γ⋆π₁⋆p,γ⋆π₂ .snd))))

    opaque
      unfolding Element ΣPsh PathPsh push-σ PshHet→ElementFunctorᴰ PshHomᴰ-map-toElt
      LR∀-repr : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
        → UniversalElement (Cᴰ / (P ×Psh Q)) (wkPshᴰ Q ⟅ (Cᴰ / P) [-, Γ , Γᴰ , toElt P p ] ⟆)
      LR∀-repr {Γ} Γᴰ p = RepresentationPshIso→UniversalElement (wkPshᴰ Q ⟅ (Cᴰ / P) [-, _ , Γᴰ , p ] ⟆)
        (((Γ ×Q) .vertex , (π₁* Γᴰ .fst , (((Γ ×Q) .element .fst P.⋆ p) , (Γ ×Q) .element .snd)))
        ,
        -- Cᴰ / P [-, Γ ×Q , π₁* Γᴰ , π₁⋆p , π₂ ]
        push-repr
        -- pushⱽ (π₁⋆p , π₂) Cᴰ [-][-, π₁* Γᴰ ]
        ⋆PshIso push-PshIsoⱽ (yoRec (P ×Psh Q) (((Γ ×Q) .element .fst) P.⋆ p , (Γ ×Q) .element .snd)) ((π₁* Γᴰ) .snd)
        -- pushⱽ (π₁⋆p , π₂) $ reindPshᴰNatTrans π₁ $ Cᴰ [-][-, Γᴰ ]
        ⋆PshIso BeckChevalley (yoRec P p) (π₁ P Q) (yoRec (P ×Psh Q) (((Γ ×Q) .element .fst) P.⋆ p , (Γ ×Q) .element .snd)) (yoRec (C [-, Γ ]) ((Γ ×Q) .element .fst)) (LR∀-pullback Γᴰ p) (Cᴰ [-][-, Γᴰ ])
        -- reindPshᴰNatTrans π₁ $ pushⱽ p $ Cᴰ [-][-, Γᴰ ]
        ⋆PshIso reindPshIso (Idᴰ /Fⱽ π₁ P Q) (invPshIso push-repr)
        -- reindPshᴰNatTrans π₁ $ (Cᴰ / P) [-, Γ , Γᴰ , p ]
        )

      wkLR∀ : Functor (Cᴰ / P) (Cᴰ / (P ×Psh Q))
      wkLR∀ = P⇒Large-cocontinuous-repr.P-F {C = Cᴰ / P}{D = Cᴰ / (P ×Psh Q)} (wkPshᴰ Q) (wkPshᴰ-cocont Q)
        λ (Γ , Γᴰ , p) → LR∀-repr Γᴰ p ◁PshIso eqToPshIso (F-ob (wkPshᴰ Q ∘F (CurryBifunctorL $ HomBif (Cᴰ / P))) _) Eq.refl Eq.refl

      ∀PshSmall : (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ) → Presheafᴰ P Cᴰ ℓPᴰ
      ∀PshSmall = reindPsh wkLR∀

    -- ∀PshSmall-UMP : ∀ (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ) {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
    --   → Iso (PshHom Rᴰ (∀PshSmall Pᴰ)) (PshHom (wkPshᴰ Q ⟅ Rᴰ ⟆) Pᴰ)
    -- ∀PshSmall-UMP Pᴰ = ∀PshSmall.P⇒Small-UMP Pᴰ _
