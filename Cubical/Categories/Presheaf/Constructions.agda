{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Terminal.Base
open import Cubical.Categories.Displayed.Presheaf.Base

private
  variable
    ℓ ℓ' ℓA ℓB ℓP ℓQ ℓS : Level

open Functor
module _ {C : Category ℓ ℓ'} where

  PshProd' : Functor
    (PresheafCategory C ℓA ×C PresheafCategory C ℓB)
    (PresheafCategory C (ℓ-max ℓA ℓB))
  PshProd' = (postcomposeF _ ×Sets ∘F ,F-functor)

  PshProd : Bifunctor (PresheafCategory C ℓA) (PresheafCategory C ℓB)
                      (PresheafCategory C (ℓ-max ℓA ℓB))
  PshProd = ParFunctorToBifunctor PshProd'

  _×Psh_ : Presheaf C ℓA → Presheaf C ℓB → Presheaf C _
  P ×Psh Q = PshProd ⟅ P , Q ⟆b

  module _ (P : Presheaf C ℓA)(Q : Presheaf C ℓB)where
    π₁ : PshHom (P ×Psh Q) P
    π₁ .fst _ = fst
    π₁ .snd _ _ _ _ = refl

    π₂ : PshHom (P ×Psh Q) Q
    π₂ .fst _ = snd
    π₂ .snd _ _ _ _ = refl

  module _ ((P , _×P) : Σ[ P ∈ Presheaf C ℓA ] ∀ c → UniversalElement C ((C [-, c ]) ×Psh P)) (Q : Presheaf C ℓB) where
    private
      module C = Category C
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    open UniversalElementNotation
    _⇒PshSmall_ : Presheaf C ℓB
    _⇒PshSmall_ .F-ob Γ = Q .F-ob ((Γ ×P) .vertex)
    _⇒PshSmall_ .F-hom {Γ}{Δ} γ q =
      intro (Γ ×P) (((Δ ×P) .element .fst C.⋆ γ) , (Δ ×P) .element .snd) Q.⋆ q
    _⇒PshSmall_ .F-id {Γ} = funExt λ q →
      Q.⟨ intro⟨_⟩ (Γ ×P) (ΣPathP (C.⋆IdR _ , refl)) ∙ (sym $ weak-η $ Γ ×P) ⟩⋆⟨⟩
      ∙ Q.⋆IdL _
    _⇒PshSmall_ .F-seq {Γ}{Δ}{Θ} γ δ = funExt λ q →
      Q.⟨
        intro≡ (Γ ×P) (ΣPathP
          ( (sym (C.⋆Assoc _ _ _) ∙ C.⟨ sym $ cong fst $ β $ Δ ×P ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _
          ∙ C.⟨ refl ⟩⋆⟨ sym $ cong fst $ β $ Γ ×P ⟩
          ∙ sym (C.⋆Assoc _ _ _))
          , (sym $ P.⋆Assoc _ _ _ ∙ P.⟨⟩⋆⟨ cong snd $ β $ Γ ×P ⟩ ∙ (cong snd $ β $ Δ ×P))
          ))
      ⟩⋆⟨⟩
      ∙ Q.⋆Assoc _ _ _
  module _ (P : Presheaf C ℓA) (Q : Presheaf C ℓB) where
    private
      module C = Category C
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    open UniversalElementNotation
    _⇒PshLarge_ : Presheaf C (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ' ℓA)) ℓB)
    _⇒PshLarge_ = (PshHomProf ⟅ Q ⟆) ∘F ((appR PshProd P ∘F YO) ^opF)
    module _ {S : Presheaf C ℓS} where
      private
        module S = PresheafNotation S
        module S×P = PresheafNotation (S ×Psh P)
      λPshHom : PshHom (S ×Psh P) Q → PshHom S (_⇒PshLarge_)
      λPshHom f⟨p⟩ .fst Γ s .fst Δ (γ , p) = f⟨p⟩ .fst Δ ((γ S.⋆ s) , p)
      λPshHom f⟨p⟩ .fst Γ s .snd Θ Δ δ (γ , p) =
        cong (f⟨p⟩ .fst Θ) (ΣPathP (S.⋆Assoc _ _ _ , refl))
        ∙ f⟨p⟩ .snd _ _ _ _
      λPshHom f⟨p⟩ .snd Θ Δ δ s = makePshHomPath (funExt (λ Ξ → funExt (λ (θ , p) →
        cong (f⟨p⟩ .fst Ξ) (ΣPathP ((sym $ S.⋆Assoc _ _ _) , refl)))))

    appPshHom : PshHom (_⇒PshLarge_ ×Psh P) Q
    appPshHom .fst Γ (f , p) = f .fst Γ (C.id , p)
    appPshHom .snd Δ Γ γ (f , p) =
      cong (f .fst Δ) (ΣPathP (C.⋆IdL _ ∙ sym (C.⋆IdR _) , refl))
      ∙ f .snd _ _ _ _

  module _ (P : Presheaf C ℓA)(_×P : ∀ c → UniversalElement C ((C [-, c ]) ×Psh P))(Q : Presheaf C ℓB) where
    private
      module C = Category C
      module P = PresheafNotation P
      module _×P c = PresheafNotation ((C [-, c ]) ×Psh P)
      module Q = PresheafNotation Q
    -- P⇒Q Γ :=
    -- PshHom (y Γ × P) Q
    -- ≅ PshHom y(Γ ×P) Q
    -- ≅ Q (Γ ×P)
    open UniversalElementNotation
    ⇒PshSmallIso⇒PshLarge : ∀ Γ
      → Iso Q.p[ (Γ ×P) .vertex ]
            (PshHom ((C [-, Γ ]) ×Psh P) Q)

    private
      module ⇒PshSmallIso⇒PshLarge Γ = Iso (⇒PshSmallIso⇒PshLarge Γ)
    ⇒PshSmallIso⇒PshLarge Γ =
      compIso
        (IsoYoRec Q ((Γ ×P) .vertex))
        (PshIso→⋆PshHomIso (invPshIso (yoRecIso (Γ ×P))))

    ⇒PshSmall≅⇒PshLarge : PshIso ((P , _×P) ⇒PshSmall Q) (P ⇒PshLarge Q)
    ⇒PshSmall≅⇒PshLarge .fst .fst = ⇒PshSmallIso⇒PshLarge.fun
    ⇒PshSmall≅⇒PshLarge .fst .snd Δ Γ γ q = makePshHomPath (funExt λ x → funExt λ p →
      (sym $ Q.⋆Assoc _ _ _)
      ∙ Q.⟨ sym $ intro≡ (Γ ×P) $ ΣPathP
        ( (C.⟨ cong fst $ sym $ β $ Δ ×P ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _) ∙ C.⟨ refl ⟩⋆⟨ cong fst $ sym $ β $ Γ ×P ⟩ ∙ sym (C.⋆Assoc _ _ _)
        , (cong snd $ sym $ β $ Δ ×P) ∙ P.⟨⟩⋆⟨ cong snd $ sym $ β $ Γ ×P ⟩ ∙ sym (P.⋆Assoc _ _ _)
        )
      ⟩⋆⟨⟩)
    ⇒PshSmall≅⇒PshLarge .snd Γ = IsoToIsIso (⇒PshSmallIso⇒PshLarge Γ)

  open Functor
  open Functorᴰ
  module _ (P : Presheaf C ℓA) (Pᴰ : Presheafᴰ P (Unitᴰ _) ℓB) where
    private
      module C = Category C
      module P = PresheafNotation P
      module Pᴰ = PresheafᴰNotation Pᴰ
    ΣPsh :  Presheaf C (ℓ-max ℓA ℓB)
    ΣPsh .F-ob x .fst = Σ[ p ∈ P.p[ x ] ] ⟨ Pᴰ .F-obᴰ _ p ⟩
    ΣPsh .F-ob x .snd = isSetΣ P.isSetPsh (λ p → Pᴰ .F-obᴰ _ _ .snd)
    ΣPsh .F-hom f (p , pᴰ) = _ , Pᴰ .F-homᴰ {f = f} _ p pᴰ
    ΣPsh .F-id = funExt λ (p , pᴰ) →
      ΣPathP (_ , λ i → Pᴰ .F-idᴰ i p pᴰ )
    ΣPsh .F-seq f g = funExt λ (p , pᴰ) →
      ΣPathP (_ , λ i → Pᴰ .F-seqᴰ {f = f}{g = g} _ _ i p pᴰ)

    -- Γ , x: p
    Comprehension : (Γ : C.ob) → P.p[ Γ ] → Presheaf C (ℓ-max ℓ' ℓB)
    Comprehension Γ p .F-ob Δ .fst =
      Σ[ γ ∈ C [ Δ , Γ ] ] Pᴰ.p[ γ P.⋆ p ][ _ ]
    Comprehension Γ p .F-ob Δ .snd = isSetΣ C.isSetHom (λ _ → Pᴰ.isSetPshᴰ)
    Comprehension Γ p .F-hom δ (γ , pᴰ) =
      (δ C.⋆ γ) , Pᴰ.reind (sym $ P.⋆Assoc _ _ _)
        (_ Pᴰ.⋆ᴰ pᴰ)
    Comprehension Γ p .F-id = funExt (λ (γ , q) → ΣPathP ((C.⋆IdL _) ,
      (Pᴰ.rectify $ Pᴰ.≡out $
        sym (Pᴰ.reind-filler _ _)
        ∙ Pᴰ.⋆IdL _)))
    Comprehension Γ p .F-seq f g = funExt λ (γ , q) → ΣPathP (C.⋆Assoc _ _ _
      , (Pᴰ.rectify $ Pᴰ.≡out $
        sym (Pᴰ.reind-filler _ _)
        ∙ Pᴰ.⋆Assoc _ _ _
        ∙ Pᴰ.⟨ refl ⟩⋆⟨ Pᴰ.reind-filler _ _ ⟩
        ∙ Pᴰ.reind-filler _ _))

  private
    open Category
    open Bifunctor
    open NatTrans
    -- Test to make sure we get the right definitional
    -- behavior for Bif-homL, Bif-homR
    module _ (P P' : Presheaf C ℓA)(Q Q' : Presheaf C ℓB)
             (α : PresheafCategory C ℓA [ P , P' ])
             (β : PresheafCategory C ℓB [ Q , Q' ])
             c where

      _ : PshProd .Bif-homL α Q .N-ob c ≡ λ (p , q) → α .N-ob c p , q
      _ = refl

      _ : PshProd .Bif-homR P β .N-ob c ≡ λ (p , q) → p , β .N-ob c q
      _ = refl
