{-
  Assume we have a presheaf P : C^op → SET ℓ and

  And we have a family P' : C.ob → Type ℓ' and for every c, an iso P c ≅ P' c.
  Then P' inherits a presheaf structure from P', and defines a presheaf P' with natural iso P ≅ P'.
-}

module Cubical.Categories.Presheaf.Constructions.IsoFib where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
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
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Bifunctor

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓP ℓQ ℓS : Level

open Category
open Functor
open PshHom
open PshIso

module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓP)(S : C .ob → Type ℓS)
  where
  private
    module P = PresheafNotation P
  pushPsh : (P≅S : ∀ c → Iso P.p[ c ] (S c)) → Presheaf C ℓS
  pushPsh P≅S .F-ob c .fst = S c
  pushPsh P≅S .F-ob c .snd = isOfHLevelRetractFromIso 2 (invIso $ P≅S c) (P .F-ob c .snd)
  pushPsh P≅S .F-hom f s = Iso.fun (P≅S _) (P .F-hom f (Iso.inv (P≅S _) s))
  pushPsh P≅S .F-id = funExt (λ s → cong (Iso.fun (P≅S _)) (P.⋆IdL _) ∙ Iso.rightInv (P≅S _) s)
  pushPsh P≅S .F-seq f g = funExt λ s →
    cong (Iso.fun (P≅S _))
      (P.⋆Assoc _ _ _
      ∙ cong (g P.⋆_) (sym $ Iso.leftInv (P≅S _) _))

  pushPshIso : (P≅S : ∀ c → Iso P.p[ c ] (S c)) → PshIso P (pushPsh P≅S)
  pushPshIso P≅S .trans .N-ob c = Iso.fun (P≅S c)
  pushPshIso P≅S .trans .N-hom c c' f p =
    cong (Iso.fun (P≅S c)) $ cong (f P.⋆_) $ sym $ Iso.leftInv (P≅S _) _
  pushPshIso P≅S .nIso c .fst = Iso.inv (P≅S c)
  pushPshIso P≅S .nIso c .snd .fst = Iso.rightInv (P≅S c)
  pushPshIso P≅S .nIso c .snd .snd = Iso.leftInv (P≅S c)

module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓP)(S : C .ob → Type ℓS)
  (_S⋆_ : ∀ {Δ Γ} → C [ Δ , Γ ] → S Γ → S Δ)
  where
  private
    module P = PresheafNotation P
  module _ (P≅S : ∀ c → Iso P.p[ c ] (S c))
    (P⋆≡S⋆ : ∀ {Δ Γ} (f : C [ Δ , Γ ]) (s : S Γ) →
      f S⋆ s ≡ P≅S Δ .Iso.fun (f P.⋆ P≅S Γ .Iso.inv s))
    where
    pushPsh' : Presheaf C ℓS
    pushPsh' .F-ob Γ .fst = S Γ
    pushPsh' .F-ob Γ .snd = isOfHLevelRetractFromIso 2 (invIso $ P≅S Γ) (P .F-ob Γ .snd)
    pushPsh' .F-hom = _S⋆_
    pushPsh' .F-id = funExt λ s →
      P⋆≡S⋆ _ _
      ∙ cong (Iso.fun (P≅S _)) (P.⋆IdL _)
      ∙ Iso.rightInv (P≅S _) s
    pushPsh' .F-seq δ γ = funExt λ s →
      P⋆≡S⋆ _ _
      ∙ cong (Iso.fun (P≅S _)) (P.⋆Assoc _ _ _
        ∙ cong (_ P.⋆_) (sym $ Iso.leftInv (P≅S _) _))
      ∙ sym (P⋆≡S⋆ _ _)
      ∙ (sym $ cong (γ S⋆_) (P⋆≡S⋆ _ _))

    pushPsh'Iso : PshIso P pushPsh'
    pushPsh'Iso .trans .N-ob = λ c → Iso.fun (P≅S c)
    pushPsh'Iso .trans .N-hom c c' f p =
      cong (Iso.fun (P≅S c)) P.⟨⟩⋆⟨ sym (Iso.leftInv (P≅S c') p) ⟩
      ∙ (sym $ P⋆≡S⋆ _ _)
    pushPsh'Iso .nIso c .fst = Iso.inv (P≅S c)
    pushPsh'Iso .nIso c .snd = Iso.rightInv (P≅S c) , Iso.leftInv (P≅S c)

    pushPsh'-singl : Σ[ P' ∈ Presheaf C ℓS ] PshIso P P'
    pushPsh'-singl = pushPsh' , pushPsh'Iso
