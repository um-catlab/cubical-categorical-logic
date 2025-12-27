{-# OPTIONS --lossy-unification #-}
{- TODO: split up this file into a bunch of individual construction files -}

{-

  Every construction on presheaves should come with
  1. A UMP which provides an interface to it
  2. A reindexing lemma that shows that it commutes with reindPshᴰNatTrans in the appropriate sense

-}

module Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions where

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

-- Products
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ {P : Presheaf C ℓP} where
    LiftPshᴰ : Presheafᴰ P Cᴰ ℓPᴰ → (ℓPᴰ' : Level) → Presheafᴰ P Cᴰ (ℓ-max ℓPᴰ ℓPᴰ')
    LiftPshᴰ Pᴰ ℓPᴰ' = LiftF {ℓ' = ℓPᴰ'} ∘F Pᴰ

    UnitPshᴰ : Presheafᴰ P Cᴰ ℓ-zero
    UnitPshᴰ = UnitPsh
    module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
      _×ⱽPsh_ : Presheafᴰ P Cᴰ (ℓ-max ℓPᴰ ℓQᴰ)
      _×ⱽPsh_ = Pᴰ ×Psh Qᴰ

      _⇒ⱽPshLarge_ : Presheafᴰ P Cᴰ (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓP) ℓPᴰ) ℓQᴰ)
      _⇒ⱽPshLarge_ = Pᴰ ⇒PshLarge Qᴰ

    -- TODO: rename: This is not weakening, wkLR∀ is.
    wkPshᴰ : (Q : Presheaf C ℓQ) → Functor (PresheafᴰCategory P Cᴰ ℓPᴰ) (PresheafᴰCategory (P ×Psh Q) Cᴰ ℓPᴰ)
    wkPshᴰ Q = reindPshF (Idᴰ /Fⱽ π₁ P Q)

    wkPshᴰ-cocont : (Q : Presheaf C ℓQ) → CoContinuous {C = (Cᴰ / P)}{D = Cᴰ / (P ×Psh Q)} (wkPshᴰ Q)
    wkPshᴰ-cocont Q = reindPshF-cocont (Idᴰ /Fⱽ π₁ P Q)

    module _ {Q : Presheaf C ℓQ} where
      private
        module ∀PshLarge = P⇒Large-cocontinuous (wkPshᴰ Q) (wkPshᴰ-cocont Q)
      module _ (PQᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ) where
        ∀PshLarge : Presheafᴰ P Cᴰ _
        ∀PshLarge = ∀PshLarge.P⇒Large PQᴰ

        -- Rᴰ(p) ⊢ ∀[ q ] PQᴰ(p,q) ≅ Rᴰ(p) ⊢ PQᴰ(p,q)
        ∀PshLarge-UMP : ∀ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
          → Iso (PshHomⱽ Rᴰ ∀PshLarge) (PshHomⱽ (wkPshᴰ Q ⟅ Rᴰ ⟆) PQᴰ)
        ∀PshLarge-UMP = ∀PshLarge.P⇒Large-UMP PQᴰ _

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    where
    _×ᴰPsh_ : (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
      → Presheafᴰ (P ×Psh Q) Cᴰ (ℓ-max ℓPᴰ ℓQᴰ)
    Pᴰ ×ᴰPsh Qᴰ = reindPshᴰNatTrans (π₁ P Q) Pᴰ ×ⱽPsh reindPshᴰNatTrans (π₂ P Q) Qᴰ

  module _ {P : Presheaf C ℓP}(Q : Presheaf C ℓQ)
    (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ) where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module Pᴰ = PresheafᴰNotation Cᴰ (P ×Psh Q) Pᴰ
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
      ΣPsh-rec : PshHomⱽ Pᴰ (wkPshᴰ Q ⟅ Rᴰ ⟆) → PshHomⱽ ΣPsh Rᴰ
      ΣPsh-rec α .N-ob (x , xᴰ , p) (q , pᴰ) = α .N-ob (x , xᴰ , p , q) pᴰ
      ΣPsh-rec α .N-hom (Δ , Δᴰ , p')(Γ , Γᴰ , p) (γ , γᴰ , γ⋆p≡p') (q , pᴰ) = α .N-hom _ _ _ _
        ∙ (Rᴰ.rectify $ Rᴰ.≡out $ Rᴰ.⋆ᴰ-reind _ _ _ ∙ (sym $ Rᴰ.⋆ᴰ-reind _ _ _))

      -- (Σ[ q ] Pᴰ(p,q) ⊢ Rᴰ(p)) ≅ Pᴰ(p,q) ⊢ Rᴰ(p)
      ΣPsh-UMP : Iso (PshHomⱽ ΣPsh Rᴰ) (PshHomⱽ Pᴰ (wkPshᴰ Q ⟅ Rᴰ ⟆))
      ΣPsh-UMP = iso (λ αⱽ → ΣPsh-σ ⋆PshHomⱽ reindPshHom (Idᴰ /Fⱽ π₁ P Q) αⱽ) ΣPsh-rec
        (λ αⱽ → makePshHomPath $ funExt λ (x , xᴰ , p , q) → funExt λ pᴰ → refl)
        λ αⱽ → makePshHomPath $ funExt λ (x , xᴰ , p) → funExt λ (q , pᴰ) → refl
  module _ (P : Presheaf C ℓP) where
    private
      module P = PresheafNotation P
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

  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} (α : PshHom P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Q = PresheafNotation Q
      module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
    -- (∃α P)(q) = Σ[ p ] Pᴰ(p) × αp ≡ q
    push : Presheafᴰ Q Cᴰ (ℓ-max ℓP (ℓ-max ℓPᴰ ℓQ))
    push = ΣPsh P (reindPshᴰNatTrans (π₂ Q P) Pᴰ ×Psh reindPshᴰNatTrans (idPshHom ×PshHom α) (PathPsh Q))

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
    -- ∃α (P × Q[α]) ⊢ ∃α P × Q
    -- ------------------------
    -- (P × Q[α]) ⊢ (∃αP × Q)[α]
    -- =============================
    -- (P × Q[α]) ⊢ ((∃αP)[α] × Q[α])
    -- ------------------------------
    -- P ⊢ ∃αP [α]      Q[α] ⊢ Q[α]
    FrobeniusReciprocity-ptwise : ∀ ((Γ , Γᴰ , q) : (Cᴰ / Q) .ob) →
      Iso (Σ[ p ∈ P.p[ Γ ] ] (Pᴰ.p[ p ][ Γᴰ ] × Qᴰ.p[ α .N-ob Γ p ][ Γᴰ ]) × (q ≡ α .N-ob Γ p))
          ((Σ[ p ∈ P.p[ Γ ] ] Pᴰ.p[ p ][ Γᴰ ] × (q ≡ α .N-ob Γ p)) × Qᴰ.p[ q ][ Γᴰ ])
    FrobeniusReciprocity-ptwise (Γ , Γᴰ , q) =
      compIso (compIso (Σ-cong-iso-snd (λ p → compIso Σ-swap-Iso (Σ-cong-iso-fst symIso))) $ invIso Σ-assoc-Iso) $
      compIso (Type.FrobeniusReciprocity (α .N-ob Γ) q) $
      Σ-cong-iso-fst (compIso Σ-assoc-Iso $ Σ-cong-iso-snd (λ p → compIso (Σ-cong-iso-fst symIso) Σ-swap-Iso) )

    FrobeniusReciprocity : PshIsoⱽ (push α (Pᴰ ×Psh reindPshᴰNatTrans α Qᴰ)) (push α Pᴰ ×Psh Qᴰ)
    FrobeniusReciprocity = Isos→PshIso FrobeniusReciprocity-ptwise
      λ (Δ , Δᴰ , q) (Γ , Γᴰ , q') (γ , γᴰ , γ⋆q≡q') (p , (pᴰ , qᴰ) , q≡αp) →
        ΣPathP ((ΣPathP (refl , refl)) , (Qᴰ.rectify $ Qᴰ.≡out $
          sym (Qᴰ.reind-filler _)
          ∙ Qᴰ.⋆ᴰ-reind _ _ _
          ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ ⟩
          ∙ sym (Qᴰ.⋆ᴰ-reind _ _ _)))

  module _
    {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
    (α : PshHom P Q)
    (β : PshIsoⱽ Pᴰ Qᴰ)
    where
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

    push-repr : ∀ {x xᴰ p}
      → PshIsoⱽ ((Cᴰ / P) [-, x , xᴰ , p ]) (pushⱽ P p (Cᴰ [-][-, xᴰ ]))
    push-repr {x}{xᴰ}{p} = pshiso (pshhom (λ (Γ , Γᴰ , q) (γ , γᴰ , γ⋆p≡q) → γ , (γᴰ , (sym $ γ⋆p≡q)))
      λ c c' f p → ΣPathP (refl , (ΣPathPProp (λ _ → P.isSetPsh _ _) (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.reind-filler _ _))))
      λ (Γ , Γᴰ , q) → (λ (f , fᴰ , q≡f⋆p) → f , (fᴰ , (sym $ q≡f⋆p)))
        , (λ _ → refl) , (λ _ → refl)

module _ {C : Category ℓC ℓC'} where
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
    (α : PshHom P R)
    (β : PshHom Q R)
    where
    Pullback : Presheaf C _
    Pullback =
      reindPsh (TotalCat.intro Id ttS) (PresheafᴰNotation.∫ (Unitᴰ C) (P ×Psh Q) (reindPshᴰNatTrans (α ×PshHom β) (PathPsh R)))

    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module R = PresheafNotation R
      module PB = PresheafNotation Pullback
      test : ∀ x → PB.p[ x ] ≡ (Σ[ (p , q) ∈ P.p[ x ] × Q.p[ x ] ] α .N-ob x p ≡ β .N-ob x q)
      test x = refl

    module _ {S : Presheaf C ℓS}
      (α' : PshHom S Q) (β' : PshHom S P)
      where
      private
        module S = PresheafNotation S
      isPullbackSq : Type _
      isPullbackSq =
        Σ[ comm ∈ (α' ⋆PshHom β) ≡ (β' ⋆PshHom α) ]
        ∀ Γ (q : Q.p[ Γ ]) → isIso {A = Σ[ s ∈ S.p[ Γ ] ] q ≡ α' .N-ob Γ s}{B = Σ[ p ∈ P.p[ Γ ] ] β .N-ob Γ q ≡ α .N-ob Γ p}
        λ (s , α's≡q) → (β' .N-ob Γ s) , cong (β .N-ob Γ) α's≡q ∙ funExt₂⁻ (cong N-ob comm) Γ s

      module _ ((_ , ispb) : isPullbackSq) {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)where
        private
          module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
        BeckChevalley-ptwise : ∀ Γ Γᴰ (q : Q.p[ Γ ])
          → Iso (Σ[ s ∈ S.p[ Γ ] ] Pᴰ.p[ β' .N-ob Γ s ][ Γᴰ ] × (q ≡ α' .N-ob Γ s))
                (Σ[ p ∈ P.p[ Γ ] ] Pᴰ.p[ p ][ Γᴰ ] × (β .N-ob Γ q ≡ α .N-ob Γ p))
        BeckChevalley-ptwise Γ Γᴰ q =
          compIso (invIso Σ-assoc-Iso) $
          compIso Σ-assoc-swap-Iso $
          compIso (Σ-cong-iso-fst (isIsoToIso (ispb Γ q))) $
          compIso Σ-assoc-swap-Iso $
          Σ-assoc-Iso

        BeckChevalley : PshIsoⱽ (push α' (reindPshᴰNatTrans β' Pᴰ)) (reindPshᴰNatTrans β (push α Pᴰ))
        BeckChevalley = Isos→PshIso (λ (Γ , Γᴰ , q) → BeckChevalley-ptwise Γ Γᴰ q)
          λ (Δ , Δᴰ , q) (Γ , Γᴰ , q') (γ , γᴰ , γ⋆q≡q') (s , pᴰ , q'≡α's) →
          ΣPathP ((β' .N-hom Δ Γ γ s) , ΣPathPProp (λ _ → R.isSetPsh _ _)
          (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.⋆ᴰ-reind _ _ _ ∙ (sym $ Pᴰ.⋆ᴰ-reind _ _ _)))

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

    LR∀-repr : ∀ {Γ} (Γᴰ : Cᴰ.ob[ Γ ]) (p : P.p[ Γ ])
      → UniversalElement (Cᴰ / (P ×Psh Q)) (wkPshᴰ Q ⟅ (Cᴰ / P) [-, Γ , Γᴰ , p ] ⟆)
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

    private
      module ∀PshSmall = P⇒Large-cocontinuous-repr {C = Cᴰ / P}{D = Cᴰ / (P ×Psh Q)} (wkPshᴰ Q) (wkPshᴰ-cocont Q) (λ (Γ , Γᴰ , p) → LR∀-repr Γᴰ p
        ◁PshIso eqToPshIso (F-ob (wkPshᴰ Q ∘F (CurryBifunctorL $ HomBif (Cᴰ / P))) _) Eq.refl Eq.refl)
    wkLR∀ : Functor (Cᴰ / P) (Cᴰ / (P ×Psh Q))
    wkLR∀ = ∀PshSmall.P-F

    ∀PshSmall : (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ) → Presheafᴰ P Cᴰ ℓPᴰ
    ∀PshSmall = reindPsh wkLR∀

    -- ∀PshSmall-UMP : ∀ (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ) {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
    --   → Iso (PshHom Rᴰ (∀PshSmall Pᴰ)) (PshHom (wkPshᴰ Q ⟅ Rᴰ ⟆) Pᴰ)
    -- ∀PshSmall-UMP Pᴰ = ∀PshSmall.P⇒Small-UMP Pᴰ _
