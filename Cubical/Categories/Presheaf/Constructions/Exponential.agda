{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor

open import Cubical.Categories.LocallySmall

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓP ℓQ ℓS : Level

open Functor
open PshHom
open PshIso

module _ {C : Category ℓ ℓ'} where
  module _ ((P , _×P) : Σ[ P ∈ Presheaf C ℓA ] LocallyRepresentable P) (Q : Presheaf C ℓB) where
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
      λPshHom f⟨p⟩ .N-ob Γ s .N-ob Δ (γ , p) = f⟨p⟩ .N-ob Δ ((γ S.⋆ s) , p)
      λPshHom f⟨p⟩ .N-ob Γ s .N-hom Θ Δ δ (γ , p) =
        cong (f⟨p⟩ .N-ob Θ) (ΣPathP (S.⋆Assoc _ _ _ , refl))
        ∙ f⟨p⟩ .N-hom _ _ _ _
      λPshHom f⟨p⟩ .N-hom Θ Δ δ s = makePshHomPath (funExt (λ Ξ → funExt (λ (θ , p) →
        cong (f⟨p⟩ .N-ob Ξ) (ΣPathP ((sym $ S.⋆Assoc _ _ _) , refl)))))

    appPshHom : PshHom (_⇒PshLarge_ ×Psh P) Q
    appPshHom .N-ob Γ (f , p) = f .N-ob Γ (C.id , p)
    appPshHom .N-hom Δ Γ γ (f , p) =
      cong (f .N-ob Δ) (ΣPathP (C.⋆IdL _ ∙ sym (C.⋆IdR _) , refl))
      ∙ f .N-hom _ _ _ _

  module _ (P : Presheaf C ℓA)(_×P : ∀ c → UniversalElement C ((C [-, c ]) ×Psh P))(Q : Presheaf C ℓB) where
    private
      module C = Category C
      module P = PresheafNotation P
      module _×P c = PresheafNotation ((C [-, c ]) ×Psh P)
      module Q = PresheafNotation Q
      module PshC = LocallySmallCategoryNotation (PRESHEAF C)
    -- P⇒Q Γ :=
    -- PshHom (y Γ × P) Q
    -- ≅ PshHom y(Γ ×P) Q
    -- ≅ Q (Γ ×P)
    open UniversalElementNotation
    ⇒PshSmallIso⇒PshLarge : ∀ Γ
      → Iso Q.p[ (Γ ×P) .vertex ]
            (PshHom ((C [-, Γ ]) ×Psh P) Q)
    ⇒PshSmallIso⇒PshLarge Γ =
      compIso
        (IsoYoRec Q ((Γ ×P) .vertex))
        ((PshC.CatIso⋆-Iso (PshC.invCatIso (asPshIso (Γ ×P)))))

    private
      module ⇒PshSmallIso⇒PshLarge Γ = Iso (⇒PshSmallIso⇒PshLarge Γ)
    ⇒PshSmall≅⇒PshLarge : PshIso ((P , _×P) ⇒PshSmall Q) (P ⇒PshLarge Q)
    ⇒PshSmall≅⇒PshLarge .trans .N-ob = ⇒PshSmallIso⇒PshLarge.fun
    ⇒PshSmall≅⇒PshLarge .trans .N-hom Δ Γ γ q = makePshHomPath (funExt λ x → funExt λ p →
      (sym $ Q.⋆Assoc _ _ _)
      ∙ Q.⟨ sym $ intro≡ (Γ ×P) $ ΣPathP
        ( (C.⟨ cong fst $ sym $ β $ Δ ×P ⟩⋆⟨ refl ⟩ ∙ C.⋆Assoc _ _ _) ∙ C.⟨ refl ⟩⋆⟨ cong fst $ sym $ β $ Γ ×P ⟩ ∙ sym (C.⋆Assoc _ _ _)
        , (cong snd $ sym $ β $ Δ ×P) ∙ P.⟨⟩⋆⟨ cong snd $ sym $ β $ Γ ×P ⟩ ∙ sym (P.⋆Assoc _ _ _)
        )
      ⟩⋆⟨⟩)
    ⇒PshSmall≅⇒PshLarge .nIso Γ = IsoToIsIso (⇒PshSmallIso⇒PshLarge Γ)
