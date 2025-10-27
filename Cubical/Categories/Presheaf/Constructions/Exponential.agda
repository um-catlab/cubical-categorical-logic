{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Constructions.Exponential where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

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
open import Cubical.Categories.Presheaf.Constructions.Restriction
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor

private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' ℓA ℓB ℓA' ℓB' ℓP ℓQ ℓS : Level

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
    _⇒PshSmall_ = restrictPsh (LRPsh→Functor (_ , _×P)) Q

    private
      module ⇒PshSmall = PresheafNotation _⇒PshSmall_
      testPshSmall : ∀ Γ → ⇒PshSmall.p[ Γ ] ≡ Q.p[ (Γ ×P) .vertex ]
      testPshSmall Γ = refl

  -- (_×P)*Q
  -- F*(_×P)*Q ≅ (F ∘ _×P)*Q ≅ (_×(F P))*(F*Q)
  --
  -- F ∘ _×P : C → D
  -- ≅ _×F*P ∘ F : C → D
    ⇒PshSmall-app : PshHom (_⇒PshSmall_ ×Psh P) Q
    ⇒PshSmall-app .N-ob c (q⟨c×P⟩ , p) = intro (c ×P) (C.id , p) Q.⋆ q⟨c×P⟩
    ⇒PshSmall-app .N-hom = {!!}
    
    module _ {S : Presheaf C ℓS} where
      private
        module S = PresheafNotation S
        module S×P = PresheafNotation (S ×Psh P)
      ⇒PshSmall-intro : PshHom (S ×Psh P) Q → PshHom S (_⇒PshSmall_)
      -- need a Q.p[ c ×P ]
      ⇒PshSmall-intro α .N-ob c s = α .N-ob ((c ×P) .vertex) (((c ×P) .element .fst S.⋆ s) , (c ×P) .element .snd)
      ⇒PshSmall-intro α .N-hom c c' f s =
        {!!}


  module _ (P : Presheaf C ℓA) (Q : Presheaf C ℓB) where
    private
      module C = Category C
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    open UniversalElementNotation
    _⇒PshLarge_ : Presheaf C (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ' ℓA)) ℓB)
    _⇒PshLarge_ = (PshHomProf ⟅ Q ⟆) ∘F ((appR PshProd P ∘F YO) ^opF)
    private
      module ⇒PshLarge = PresheafNotation _⇒PshLarge_
      testPshLarge : ∀ Γ → ⇒PshLarge.p[ Γ ] ≡ PshHom ((C [-, Γ ]) ×Psh P) Q
      testPshLarge Γ = refl

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
        (PshIso→⋆PshHomIso (invPshIso (yoRecIso (Γ ×P))))

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

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D)
  ((P , _×P) : LocallyRepresentablePresheaf D ℓP)
  (_×F*P : LocallyRepresentable (restrictPsh F P))
  (Q : Presheaf D ℓQ)
  where
  private
    module Q = PresheafNotation Q
  restrictPsh⇒Small :
    PshIso (restrictPsh F ((P , _×P) ⇒PshSmall Q))
           ((restrictPsh F P , _×F*P) ⇒PshSmall restrictPsh F Q)
  restrictPsh⇒Small .trans = ⇒PshSmall-intro (restrictPsh F P , _×F*P) (restrictPsh F Q)
    (invPshIso (restrictPsh× F ((P , _×P) ⇒PshSmall Q) P) .trans ⋆PshHom restrictPshHom F (⇒PshSmall-app (P , _×P) Q))
  restrictPsh⇒Small .nIso c .fst q⟨c×F*P⟩ = {!!} Q.⋆ q⟨c×F*P⟩
  restrictPsh⇒Small .nIso c .snd = {!!}
  -- module _ ((P , _×P) : Σ[ P ∈ Presheaf C ℓA ] LocallyRepresentable P) (Q : Presheaf C ℓB) where
