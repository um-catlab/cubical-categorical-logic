-- TODO: rewrite this to use Constructions.RightAdjoint
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
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓP ℓQ ℓR ℓS : Level

open Functor
open PshHom
open PshIso

module _ {C : Category ℓ ℓ'} where
  module _ ((P , _×P) : LRPresheaf C ℓP) (Q : Presheaf C ℓB) where
    private
      module C = Category C
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    open UniversalElementNotation
    _⇒PshSmall_ : Presheaf C ℓB
    _⇒PshSmall_ = reindPsh (LRPsh→Functor (P , _×P)) Q

    private
      module P⇒Q = PresheafNotation _⇒PshSmall_
      test⇒PshSmall : ∀ c → P⇒Q.p[ c ] ≡ Q.p[ (c ×P) .vertex ]
      test⇒PshSmall c = refl

  module _ (P : Presheaf C ℓA) (Q : Presheaf C ℓB) where
    private
      module C = Category C
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    open UniversalElementNotation
    _⇒PshLarge_ : Presheaf C (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ' ℓA)) ℓB)
    _⇒PshLarge_ = (PshHomPsh Q) ∘F ((appR PshProd P ∘F YO) ^opF)

    private
      module P⇒Q = PresheafNotation _⇒PshLarge_
      test⇒PshLarge : ∀ c → P⇒Q.p[ c ] ≡ PshHom ((C [-, c ]) ×Psh P) Q
      test⇒PshLarge c = refl

    -- under what circumstances
    -- (P ⇒PshLarge Q) ∘ F
    -- ≅ (P ∘ F) ⇒PshLarge (Q ∘ F) ?
    --
    -- Let's try;
    -- (P ⇒PshLarge Q) ∘ F
    -- = (PshHomPsh Q) ∘ ((appR PshProd P ∘ YO) ^opF) ∘ F
    -- ≅ (PshHomPsh Q) ∘ ((appR PshProd P ∘ YO) ∘ F  ^opF) ^opF

    appPshHom : PshHom (_⇒PshLarge_ ×Psh P) Q
    appPshHom .N-ob Γ (f , p) = f .N-ob Γ (C.id , p)
    appPshHom .N-hom Δ Γ γ (f , p) =
      cong (f .N-ob Δ) (ΣPathP (C.⋆IdL _ ∙ sym (C.⋆IdR _) , refl))
      ∙ f .N-hom _ _ _ _

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

      ⇒PshLarge-UMP :
        Iso (PshHom S _⇒PshLarge_)
            (PshHom (S ×Psh P) Q)
      ⇒PshLarge-UMP .Iso.fun α = ×PshIntro (π₁ S P ⋆PshHom α) (π₂ S P) ⋆PshHom appPshHom
      ⇒PshLarge-UMP .Iso.inv = λPshHom
      ⇒PshLarge-UMP .Iso.sec α⟨s,p⟩ = makePshHomPath $ funExt λ x → funExt λ (s , p) →
        cong (α⟨s,p⟩ .N-ob x) (ΣPathP ((S.⋆IdL s) , refl))
      ⇒PshLarge-UMP .Iso.ret α = makePshHomPath $ funExt λ x → funExt λ s →
        makePshHomPath $ funExt λ y → funExt λ (f , p) →
          funExt⁻ (funExt⁻ (cong N-ob (α .N-hom y x f _)) _) _
          ∙ cong (α .N-ob x s .N-ob y) (ΣPathP ((C.⋆IdL f) , refl))

  module _ ((P , _×P) : LRPresheaf C ℓP) (Q : Presheaf C ℓB) where
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
        (precomp⋆PshHom-Iso (invPshIso (yoRecIso (Γ ×P))))

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

    appPshSmall : PshHom (((P , _×P) ⇒PshSmall Q) ×Psh P) Q
    appPshSmall = (⇒PshSmall≅⇒PshLarge .trans ×PshHom idPshHom) ⋆PshHom appPshHom P Q

    -- TODO: fixup the definitions of λ/app for ⇒PshSmall if they have too many transports
    module _ {S : Presheaf C ℓS} where
      private
        module S = PresheafNotation S
      ⇒PshSmall-UMP :
        Iso (PshHom S ((P , _×P) ⇒PshSmall Q))
            (PshHom (S ×Psh P) Q)
      ⇒PshSmall-UMP =
        compIso (postcomp⋆PshHom-Iso ⇒PshSmall≅⇒PshLarge)
                (⇒PshLarge-UMP P Q)
