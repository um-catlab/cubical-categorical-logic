-- Product of two categories

module Cubical.Categories.Constructions.BinProduct.Monoidal where

import Cubical.Categories.Constructions.BinProduct as BP

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Functors.More

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level

open NatTrans
open NatIso
open isIso
module _ (M : MonoidalCategory ℓC ℓC') (N : MonoidalCategory ℓD ℓD') where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
  _×M_ : MonoidalCategory (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  _×M_ .MonoidalCategory.C = M.C BP.×C N.C
  _×M_ .MonoidalCategory.monstr .MonoidalStr.tenstr .TensorStr.─⊗─ =
    (M.─⊗─ ∘F (BP.Fst M.C N.C BP.×F BP.Fst M.C N.C))
    BP.,F (N.─⊗─ ∘F (BP.Snd M.C N.C BP.×F BP.Snd M.C N.C))
  _×M_ .MonoidalCategory.monstr .MonoidalStr.tenstr .TensorStr.unit =
    M.unit , N.unit
  _×M_ .MonoidalCategory.monstr .MonoidalStr.α .trans .N-ob x =
    M.α .trans ⟦ _ ⟧ , N.α .trans ⟦ _ ⟧
  _×M_ .MonoidalCategory.monstr .MonoidalStr.α .trans .N-hom f =
    ΣPathP ((M.α .trans .N-hom _) , (N.α .trans .N-hom _))
  _×M_ .MonoidalCategory.monstr .MonoidalStr.α .nIso x .inv =
    M.α⁻¹⟨ _ , _ , _ ⟩ , N.α⁻¹⟨ _ , _ , _ ⟩
  _×M_ .MonoidalCategory.monstr .MonoidalStr.α .nIso x .sec =
    ΣPathP ((M.α .nIso _ .sec) , (N.α .nIso _ .sec))
  _×M_ .MonoidalCategory.monstr .MonoidalStr.α .nIso x .ret =
    ΣPathP ((M.α .nIso _ .ret) , (N.α .nIso _ .ret))
  _×M_ .MonoidalCategory.monstr .MonoidalStr.η .trans .N-ob x =
    M.η⟨ _ ⟩ , N.η⟨ _ ⟩
  _×M_ .MonoidalCategory.monstr .MonoidalStr.η .trans .N-hom x =
    ΣPathP (M.η .trans .N-hom _ , N.η .trans .N-hom _)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.η .nIso x .inv =
    M.η⁻¹⟨ _ ⟩ , N.η⁻¹⟨ _ ⟩
  _×M_ .MonoidalCategory.monstr .MonoidalStr.η .nIso x .sec =
    ΣPathP (M.η .nIso _ .sec , N.η .nIso _ .sec)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.η .nIso x .ret =
    ΣPathP (M.η .nIso _ .ret , N.η .nIso _ .ret)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.ρ .trans .N-ob x =
    M.ρ⟨ _ ⟩ , N.ρ⟨ _ ⟩
  _×M_ .MonoidalCategory.monstr .MonoidalStr.ρ .trans .N-hom x =
    ΣPathP (M.ρ .trans .N-hom _ , N.ρ .trans .N-hom _)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.ρ .nIso x .inv =
    M.ρ⁻¹⟨ _ ⟩ , N.ρ⁻¹⟨ _ ⟩
  _×M_ .MonoidalCategory.monstr .MonoidalStr.ρ .nIso x .sec =
    ΣPathP (M.ρ .nIso _ .sec , N.ρ .nIso _ .sec)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.ρ .nIso x .ret =
    ΣPathP (M.ρ .nIso _ .ret , N.ρ .nIso _ .ret)
  _×M_ .MonoidalCategory.monstr .MonoidalStr.pentagon _ _ _ _ =
    ΣPathP ((M.pentagon _ _ _ _ ) , (N.pentagon _ _ _ _))
  _×M_ .MonoidalCategory.monstr .MonoidalStr.triangle _ _ =
    ΣPathP (M.triangle _ _ , N.triangle _ _)

  open Functor
  open StrongMonoidalFunctor
  open StrongMonoidalStr
  open LaxMonoidalStr
  -- Probably should be able to do this with a transport but I'll just
  -- do it manually
  Fst : StrongMonoidalFunctor _×M_ M
  Fst .F .F-ob = fst
  Fst .F .F-hom = fst
  Fst .F .F-id = refl
  Fst .F .F-seq _ _ = refl
  Fst .strmonstr .laxmonstr .ε = M.id
  Fst .strmonstr .laxmonstr .μ .N-ob = λ _ → M.id
  Fst .strmonstr .laxmonstr .μ .N-hom = λ _ → M.⋆IdR _ ∙ sym (M.⋆IdL _)
  Fst .strmonstr .laxmonstr .αμ-law _ _ _ =
    M.⋆IdR _ ∙ cong₂ M._⋆_ refl (M.─⊗─ .F-id) ∙ M.⋆IdR _
    ∙ sym (M.⋆IdL _)
    ∙ cong₂ M._⋆_ (sym (M.⋆IdR _ ∙ M.─⊗─ .F-id)) refl
  Fst .strmonstr .laxmonstr .ηε-law _ =
    cong₂ M._⋆_ (M.⋆IdR _ ∙ M.─⊗─ .F-id) refl ∙ M.⋆IdL _
  Fst .strmonstr .laxmonstr .ρε-law _ =
    cong₂ M._⋆_ ((M.⋆IdR _ ∙ M.─⊗─ .F-id)) refl ∙ M.⋆IdL _
  Fst .strmonstr .ε-isIso = idCatIso .snd
  Fst .strmonstr .μ-isIso = λ _ → idCatIso .snd

  Snd : StrongMonoidalFunctor _×M_ N
  Snd .F .F-ob = snd
  Snd .F .F-hom = snd
  Snd .F .F-id = refl
  Snd .F .F-seq _ _ = refl
  Snd .strmonstr .laxmonstr .ε = N.id
  Snd .strmonstr .laxmonstr .μ .N-ob = λ _ → N.id
  Snd .strmonstr .laxmonstr .μ .N-hom = λ _ → N.⋆IdR _ ∙ sym (N.⋆IdL _)
  Snd .strmonstr .laxmonstr .αμ-law _ _ _ =
    N.⋆IdR _ ∙ cong₂ N._⋆_ refl (N.─⊗─ .F-id) ∙ N.⋆IdR _
    ∙ sym (N.⋆IdL _)
    ∙ cong₂ N._⋆_ (sym (N.⋆IdR _ ∙ N.─⊗─ .F-id)) refl
  Snd .strmonstr .laxmonstr .ηε-law _ =
    cong₂ N._⋆_ (N.⋆IdR _ ∙ N.─⊗─ .F-id) refl ∙ N.⋆IdL _
  Snd .strmonstr .laxmonstr .ρε-law _ =
    cong₂ N._⋆_ ((N.⋆IdR _ ∙ N.─⊗─ .F-id)) refl ∙ N.⋆IdL _
  Snd .strmonstr .ε-isIso = idCatIso .snd
  Snd .strmonstr .μ-isIso = λ _ → idCatIso .snd

module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
         {O : MonoidalCategory ℓE ℓE'}
         (G : StrongMonoidalFunctor M N)(H : StrongMonoidalFunctor M O)
  where
  private
    module G = StrongMonoidalFunctor G
    module H = StrongMonoidalFunctor H
  open StrongMonoidalFunctor
  open StrongMonoidalStr
  open LaxMonoidalStr
  _,F_ : StrongMonoidalFunctor M (N ×M O)
  _,F_ .F = G.F BP.,F H.F
  _,F_ .strmonstr .laxmonstr .ε = G.ε , H.ε
  _,F_ .strmonstr .laxmonstr .μ .N-ob x = (N-ob G.μ x) , (N-ob H.μ x)
  _,F_ .strmonstr .laxmonstr .μ .N-hom f =
    ΣPathP ((N-hom G.μ f) , (N-hom H.μ f))
  _,F_ .strmonstr .laxmonstr .αμ-law x y z =
    ΣPathP ((G.αμ-law x y z) , (H.αμ-law x y z))
  _,F_ .strmonstr .laxmonstr .ηε-law x = ΣPathP (G.ηε-law x , H.ηε-law x)
  _,F_ .strmonstr .laxmonstr .ρε-law x = ΣPathP (G.ρε-law x , H.ρε-law x)
  _,F_ .strmonstr .ε-isIso .inv = (G.ε-isIso .inv) , (H.ε-isIso .inv)
  _,F_ .strmonstr .ε-isIso .sec = ΣPathP ((G.ε-isIso .sec) , (H.ε-isIso .sec))
  _,F_ .strmonstr .ε-isIso .ret = ΣPathP ((G.ε-isIso .ret) , (H.ε-isIso .ret))
  _,F_ .strmonstr .μ-isIso x .inv = (G.μ-isIso x .inv) , (H.μ-isIso x .inv)
  _,F_ .strmonstr .μ-isIso x .sec =
    ΣPathP ((G.μ-isIso x .sec) , (H.μ-isIso x .sec))
  _,F_ .strmonstr .μ-isIso x .ret =
    ΣPathP (G.μ-isIso x .ret , H.μ-isIso x .ret)

module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
         {O : MonoidalCategory ℓE ℓE'}{P : MonoidalCategory ℓB ℓB'}
         (G : StrongMonoidalFunctor M N)(H : StrongMonoidalFunctor O P)
  where
  open StrongMonoidalFunctor
  open LaxMonoidalStr
  open StrongMonoidalStr
  private
    module G = StrongMonoidalFunctor G
    module H = StrongMonoidalFunctor H

  -- would be definable using composition of strongmonoidal functors,
  -- but that's not done yet
  _×F_ : StrongMonoidalFunctor (M ×M O) (N ×M P)
  _×F_ .F = G .F BP.×F H .F
  _×F_ .strmonstr .laxmonstr .ε = G.ε , H.ε
  _×F_ .strmonstr .laxmonstr .μ .N-ob _ = (G.μ ⟦ _ ⟧) , H.μ ⟦ _ ⟧
  _×F_ .strmonstr .laxmonstr .μ .N-hom _ =
    ΣPathP ((G.μ .N-hom _) , (H.μ .N-hom _))
  _×F_ .strmonstr .laxmonstr .αμ-law _ _ _ =
    ΣPathP (G.αμ-law _ _ _ , H.αμ-law _ _ _ )
  _×F_ .strmonstr .laxmonstr .ηε-law _ = ΣPathP (G.ηε-law _ , H.ηε-law _ )
  _×F_ .strmonstr .laxmonstr .ρε-law _ = ΣPathP (G.ρε-law _ , H.ρε-law _ )
  _×F_ .strmonstr .ε-isIso .inv = G.ε-isIso .inv , H.ε-isIso .inv
  _×F_ .strmonstr .ε-isIso .sec = ΣPathP (G.ε-isIso .sec , H.ε-isIso .sec)
  _×F_ .strmonstr .ε-isIso .ret = ΣPathP (G.ε-isIso .ret , H.ε-isIso .ret)
  _×F_ .strmonstr .μ-isIso _ .inv = G.μ-isIso _ .inv , H.μ-isIso _ .inv
  _×F_ .strmonstr .μ-isIso _ .sec = ΣPathP (G.μ-isIso _ .sec , H.μ-isIso _ .sec)
  _×F_ .strmonstr .μ-isIso _ .ret = ΣPathP (G.μ-isIso _ .ret , H.μ-isIso _ .ret)
