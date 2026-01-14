{-# OPTIONS --lossy-unification #-}
{- TODO: split up this file into a bunch of individual construction files -}

{-

  Every construction on presheaves should come with
  1. A UMP which provides an interface to it
  2. A reindexing lemma that shows that it commutes with reindPshᴰNatTrans in the appropriate sense

-}

module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Push where

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

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Sigma
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Path

-- Products
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} (α : PshHom P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Q = PresheafNotation Q
      module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ

    -- (∃α P)(q) = Σ[ p ] Pᴰ(p) × αp ≡ q
    push : Presheafᴰ Q Cᴰ (ℓ-max ℓP (ℓ-max ℓPᴰ ℓQ))
    push = ΣPsh P (reindPshᴰNatTrans (π₂ Q P) Pᴰ ×Psh reindPshᴰNatTrans (idPshHom ×PshHom α) (PathPsh Q))

    opaque
      unfolding Element ΣPsh PathPsh PshHet→ElementFunctorᴰ PshHomᴰ-map-toElt
        PresheafᴰNotation.⋆IdLᴰ
      -- Pᴰ ⊢ (∃α Pᴰ)[α]
      -- ===============================
      -- Pᴰ(p) ⊢ (Σ[ p' ] Pᴰ(p') × αp'≡q)[αp/q]
      -- ===============================
      -- Pᴰ(p) ⊢ Σ[ p' ] (Pᴰ(p') × αp'≡q)[αp/q]
      -- ===============================
      -- Pᴰ(p) ⊢ Σ[ p' ] Pᴰ(p')[αp/q] × αp'≡q[αp/q]
      -- ===============================
      -- Pᴰ(p) ⊢ (Σ[ p' ] Pᴰ(p') × αp'≡αp)
      -- ===============================
      -- Pᴰ(p) ⊢ (Σ[ p' ] Pᴰ(p') × αp'≡αp)
      push-σ : PshHomᴰ α Pᴰ push
      push-σ .N-ob (Γ , Γᴰ , p) pᴰ = p , (pᴰ , refl)
      push-σ .N-hom _ _ (γ , Γᴰ , γ⋆p≡p') pᴰ = ΣPathP ((sym $ γ⋆p≡p') , (ΣPathPProp (λ _ → Q.isSetPsh _ _)
        (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.⋆ᴰ-reind _ _ _ ∙ (sym $ Pᴰ.⋆ᴰ-reind _ _ _))))

  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} (α : PshHom P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ} where
    private
      module Q = PresheafNotation Q
      module Qᴰ = PresheafᴰNotation Cᴰ Q Qᴰ

    opaque
      unfolding Element ΣPsh PathPsh push-σ PshHet→ElementFunctorᴰ PshHomᴰ-map-toElt
        PresheafᴰNotation.⋆IdLᴰ makePshHomᴰPath
      -- TODO: less manual definition?
      push-recⱽ : PshHomᴰ α Pᴰ Qᴰ → PshHomⱽ (push α Pᴰ) Qᴰ
      push-recⱽ αᴰ .N-ob (Γ , Γᴰ , q) (p , pᴰ , q≡αp) = Qᴰ .F-hom ((C .id) , ((Categoryᴰ.idᴰ Cᴰ) , (Q.⋆IdL _ ∙ (sym $ q≡αp)))) $ αᴰ .N-ob (Γ , Γᴰ , p) pᴰ
      push-recⱽ αᴰ .N-hom (Δ , Δᴰ , q) (Γ , Γᴰ , q') (γ , γᴰ , γ⋆q'≡q) (p , pᴰ , q'≡αp) = Qᴰ.rectify $ Qᴰ.≡out $
        Qᴰ.⋆ᴰ-reind _ _ _
        ∙ Qᴰ.⟨⟩⋆⟨ (Qᴰ.≡in $ αᴰ .N-hom _ _ _ _) ∙ Qᴰ.⋆ᴰ-reind _ _ _ ⟩
        ∙ sym (Qᴰ.⋆Assoc _ _ _)
        ∙ Qᴰ.⟨ Cᴰ.⋆IdL _ ⟩⋆⟨ (sym $ Qᴰ.⋆IdL _) ∙ sym (Qᴰ.⋆ᴰ-reind Cᴰ.idᴰ _ (αᴰ .N-ob (Γ , Γᴰ , p) pᴰ)) ⟩
        ∙ sym (Qᴰ.⋆ᴰ-reind γᴰ γ⋆q'≡q _)

      push-UMP : Iso (PshHomⱽ (push α Pᴰ) Qᴰ) (PshHomᴰ α Pᴰ Qᴰ)
      push-UMP = iso
        (λ βⱽ → push-σ α Pᴰ ⋆PshHom reindPshHom (Idᴰ /Fⱽ α) βⱽ)
        push-recⱽ
        (λ βⱽ → makePshHomPath (funExt λ (Γ , Γᴰ , p) → funExt λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.⋆ᴰ-reind _ _ _ ∙ Qᴰ.⋆IdL _))
        (λ βⱽ → makePshHomPath (funExt λ (Γ , Γᴰ , q) → funExt (λ (p , pᴰ , q≡αp) → Qᴰ.rectify $ Qᴰ.≡out $
          Qᴰ.⋆ᴰ-reind _ _ _ ∙ Qᴰ.⋆IdL _
          ∙ ΣPathP (sym q≡αp , λ i → βⱽ .N-ob (Γ , (Γᴰ , q≡αp (~ i))) (p , pᴰ , λ j → q≡αp ((~ i) ∨ j))))))

  pushⱽ : ∀ (P : Presheaf C ℓP) {x} (p : ⟨ P ⟅ x ⟆ ⟩ )(Pⱽ : Presheafⱽ x Cᴰ ℓPᴰ) → Presheafᴰ P Cᴰ (ℓ-max ℓC' (ℓ-max ℓPᴰ ℓP))
  pushⱽ P p Pⱽ = push (yoRec P p) Pⱽ

  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}(α : PshHom P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
      module Qᴰ = PresheafᴰNotation Cᴰ Q Qᴰ

    opaque
      unfolding Element ΣPsh PathPsh push-σ PshHet→ElementFunctorᴰ PshHomᴰ-map-toElt
        PresheafᴰNotation.⋆IdLᴰ makePshHomᴰPath
      -- ∃α (P × Q[α]) ⊢ ∃α P × Q
      -- ------------------------
      -- (P × Q[α]) ⊢ (∃αP × Q)[α]
      -- =============================
      -- (P × Q[α]) ⊢ ((∃αP)[α] × Q[α])
      -- ------------------------------
      -- P ⊢ ∃αP [α]      Q[α] ⊢ Q[α]
      FrobeniusReciprocity-ptwise : ∀ ((Γ , Γᴰ , q) : (Cᴰ / Q) .ob) →
        Iso (Σ[ p ∈ P.p[ Γ ] ] (Pᴰ.p[ p ][ Γᴰ ]
                              × Qᴰ.p[ α .N-ob Γ p ][ Γᴰ ])
                              × (q ≡ toElt Q (α .N-ob Γ p)))
            ((Σ[ p ∈ P.p[ Γ ] ] Pᴰ.p[ p ][ Γᴰ ]
                             × (q ≡ toElt Q (α .N-ob Γ p)))
              × Qᴰ.p[ fromElt Q q ][ Γᴰ ])
      FrobeniusReciprocity-ptwise (Γ , Γᴰ , q) .fun (p , (pᴰ , qᴰ) , q≡αΓp) = (p , pᴰ , q≡αΓp) , Qᴰ.reind (sym q≡αΓp) qᴰ
      FrobeniusReciprocity-ptwise (Γ , Γᴰ , q) .inv ((p , pᴰ , q≡αΓp), qᴰ) = p , ((pᴰ , (Qᴰ.reind q≡αΓp qᴰ)) , q≡αΓp)
      FrobeniusReciprocity-ptwise (Γ , Γᴰ , q) .sec ((p , pᴰ , q≡αΓp), qᴰ) =
        ΣPathP (refl , (Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ ∙ Qᴰ.reind-filler _))
      FrobeniusReciprocity-ptwise (Γ , Γᴰ , q) .ret (p , (pᴰ , qᴰ) , q≡αΓp) =
        ΣPathP (refl , ΣPathP ((ΣPathP (refl , (Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ ∙ Qᴰ.reind-filler _))) , refl))

      FrobeniusReciprocity-natural-ty :
        (Δ,Δᴰ,q : (Cᴰ / Q) .ob) →
        (Γ,Γᴰ,q' : (Cᴰ / Q) .ob) →
        (γ,γᴰ,γ⋆q≡q' : (Cᴰ / Q) [ Δ,Δᴰ,q , Γ,Γᴰ,q' ]) →
        (p,⟨pᴰ,qᴰ⟩,q≡αp :
          PresheafNotation.p[ push α (Pᴰ ×Psh reindPshᴰNatTrans α Qᴰ) ] Γ,Γᴰ,q') →
        Type (ℓ-max (ℓ-max (ℓ-max ℓP ℓQ) ℓPᴰ) ℓQᴰ)
      FrobeniusReciprocity-natural-ty Δ,Δᴰ,q Γ,Γᴰ,q' γ,γᴰ,γ⋆q≡q' p,⟨pᴰ,qᴰ⟩,q≡αp =
          (fun (FrobeniusReciprocity-ptwise Δ,Δᴰ,q)
          ((push α (Pᴰ ×Psh reindPshᴰNatTrans α Qᴰ) PresheafNotation.⋆
            γ,γᴰ,γ⋆q≡q') p,⟨pᴰ,qᴰ⟩,q≡αp)
          ≡
          ((push α Pᴰ ×Psh Qᴰ) PresheafNotation.⋆ γ,γᴰ,γ⋆q≡q')
          (fun (FrobeniusReciprocity-ptwise Γ,Γᴰ,q') p,⟨pᴰ,qᴰ⟩,q≡αp))

      FrobeniusReciprocity-natural : ∀ Δ,Δᴰ,q Γ,Γᴰ,q' γ,γᴰ,γ⋆q≡q' p,⟨pᴰ,qᴰ⟩,q≡αp →
        FrobeniusReciprocity-natural-ty Δ,Δᴰ,q Γ,Γᴰ,q' γ,γᴰ,γ⋆q≡q' p,⟨pᴰ,qᴰ⟩,q≡αp

      FrobeniusReciprocity-natural Δ,Δᴰ,q Γ,Γᴰ,q' γ,γᴰ,γ⋆q≡q' p,⟨pᴰ,qᴰ⟩,q≡αp =
        ΣPathP ((ΣPathP (refl , refl)) , (Qᴰ.rectify $ Qᴰ.≡out $
          sym (Qᴰ.reind-filler _)
          ∙ Qᴰ.⋆ᴰ-reind _ _ _
          ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ ⟩
          ∙ sym (Qᴰ.⋆ᴰ-reind _ _ _)))

      FrobeniusReciprocity : PshIsoⱽ (push α (Pᴰ ×Psh reindPshᴰNatTrans α Qᴰ)) (push α Pᴰ ×Psh Qᴰ)
      FrobeniusReciprocity = Isos→PshIso FrobeniusReciprocity-ptwise FrobeniusReciprocity-natural

  module _
    {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
    (α : PshHom P Q)
    (β : PshIsoⱽ Pᴰ Qᴰ)
    where

    opaque
      unfolding Element ΣPsh PathPsh push-σ PshHet→ElementFunctorᴰ PshHomᴰ-map-toElt
        PresheafᴰNotation.⋆IdLᴰ makePshHomᴰPath
      -- just functoriality, derivable from functoriality of the components of push.
      -- Probably wait until we port to locally small stuff
      push-PshIsoⱽ : PshIsoⱽ (push α Pᴰ) (push α Qᴰ)
      push-PshIsoⱽ = Isos→PshIso
        (λ (Γ , Γᴰ , q) → Σ-cong-iso-snd (λ p → Σ-cong-iso-fst (PshIso→Isos β (Γ , (Γᴰ , p)))))
        λ (Δ , Δᴰ , q)(Γ , Γᴰ , q') (γ , γᴰ , γ⋆q≡q')(p , pᴰ , q'≡αp) → ΣPathP (refl , (ΣPathPProp (λ _ → PresheafNotation.isSetPsh Q _ _)
        (β .trans .N-hom _ _ _ _)))

  module _ {P : Presheaf C ℓP} where
    private
      module P = PresheafNotation P

    opaque
      unfolding Element ΣPsh PathPsh push-σ PshHet→ElementFunctorᴰ PshHomᴰ-map-toElt
        PresheafᴰNotation.⋆IdLᴰ makePshHomᴰPath Curry.UncurryPshᴰ Curry.CurryPshᴰ
      push-repr : ∀ {x xᴰ p}
        → PshIsoⱽ ((Cᴰ / P) [-, x , xᴰ , p ]) (pushⱽ P (fromElt P p) (Cᴰ [-][-, xᴰ ]))
      push-repr {x}{xᴰ}{p} = pshiso (pshhom (λ (Γ , Γᴰ , q) (γ , γᴰ , γ⋆p≡q) → γ , (γᴰ , (sym $ γ⋆p≡q)))
        λ c c' f p → ΣPathP (refl , (ΣPathPProp (λ _ → P.isSetPsh _ _) (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.reind-filler _ _))))
        λ (Γ , Γᴰ , q) → (λ (f , fᴰ , q≡f⋆p) → f , (fᴰ , (sym $ q≡f⋆p)))
          , (λ _ → refl) , (λ _ → refl)

opaque
  unfolding push-σ unfoldPresheafᴰDefs push-recⱽ
    FrobeniusReciprocity push-PshIsoⱽ push-repr
  unfoldPushDefs : Unit
  unfoldPushDefs = tt
